import SphincsSecurity.Proof.ParentReserveBound
import SphincsSecurity.Proof.FirstOtsParentGame

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
open OtsProbeSimulation (IsOtsPosition OtsExceptionRecord SampledFirstOtsParentRecord otsHashInputCharge)

attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def ftsParentQueryCharge (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : ℝ≥0∞ :=
  parentReserveCharge secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
    (fun position => ¬ IsOtsPosition position) cache input

def SampledFirstFtsParentRecord
    (result : SampledSecrets × ((Bool × QueryCache HashSpec) × Option ExceptionRecord)) : Prop :=
  ∃ record ∈ result.2.2, EligibleParentRecord result.1.parameter (fun position => ¬ IsOtsPosition position) record

theorem probEvent_sampledFirstFtsParentRecord_le_queryCharge (adversary : Adversary) :
    Pr[SampledFirstFtsParentRecord | sampledFirstParentSettlementGame adversary] ≤
      sampledQueryCharge ftsParentQueryCharge adversary * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [sampledFirstParentSettlementGame, probEvent_bind_eq_tsum, sampledQueryCharge, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro secrets
  rw [mul_assoc]
  apply mul_le_mul' le_rfl
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, SampledFirstFtsParentRecord]
  unfold ftsParentQueryCharge
  exact probEvent_firstEligibleParentRecord_le_queryCharge secrets.parameter secrets.otsSecret secrets.ftsSecret
      (fun position => ¬ IsOtsPosition position)
      (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret)

theorem OtsProbeSimulation.IsOtsPosition.of_parent {child parent : Position}
    (hparent : child.parentOf = some parent) (hots : IsOtsPosition parent) : IsOtsPosition child := by
  cases child with
  | chain | leaf | node => trivial
  | ftsLeaf =>
      simp only [Position.parentOf, Option.some.injEq] at hparent
      subst parent
      exact hots
  | ftsNode =>
      simp only [Position.parentOf] at hparent
      split_ifs at hparent <;> cases Option.some.inj hparent <;> exact hots
  | ftsRoots => simp [Position.parentOf] at hparent

theorem sampledFirstParentRecord_ots_or_fts (adversary : Adversary)
    {result : SampledSecrets × ((Bool × QueryCache HashSpec) × Option ExceptionRecord)}
    (hresult : result ∈ support (sampledFirstParentSettlementGame adversary))
    (hhit : result.2.2.isSome = true) :
    SampledFirstOtsParentRecord result ∨ SampledFirstFtsParentRecord result := by
  classical
  obtain ⟨record, hrecord⟩ := Option.isSome_iff_exists.mp hhit
  have hmem : record ∈ result.2.2 := by simp [hrecord]
  have hvalid := sampledFirstParentSettlementGame_record_valid adversary hresult hmem
  obtain ⟨_, child, parent, hat, _, _, hparent, _⟩ := hvalid.2.2.1.2
  by_cases hots : IsOtsPosition parent
  · exact Or.inl ⟨record, hmem, child, hat, hots.of_parent hparent⟩
  · exact Or.inr ⟨record, hmem, child, parent, hat, hparent, hots⟩

theorem probEvent_sampledFirstParentRecord_le_queryCharges (adversary : Adversary)
    (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest) :
    Pr[fun result => result.2.2.isSome = true | sampledFirstParentSettlementGame adversary] ≤
      (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary *
        OtsProbeSimulation.privateHistoryGuessRate q + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) +
      sampledQueryCharge ftsParentQueryCharge adversary * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply (probEvent_mono (p := fun result => result.2.2.isSome = true)
    (q := fun result => SampledFirstOtsParentRecord result ∨ SampledFirstFtsParentRecord result)
    (fun _ hresult hhit => sampledFirstParentRecord_ots_or_fts adversary hresult hhit)).trans
  exact (probEvent_or_le _ _ _).trans (add_le_add
    (OtsProbeSimulation.probEvent_sampledFirstOtsParentRecord_le_actualOtsCount_rate_add_erasure adversary q hq hqSpace)
    (probEvent_sampledFirstFtsParentRecord_le_queryCharge adversary))

theorem ots_ftsLeaf_parent_queryCharge_le_one (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) :
    otsHashInputCharge secretKey.parameter input + FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter cache input +
      ftsParentQueryCharge secretKey cache input ≤ 1 := by
  classical
  by_cases hots : ∃ position, IsOtsPosition position ∧ AtPosition secretKey.parameter input position
  · obtain ⟨position, hp, hat⟩ := hots
    have hnotParent : ¬ ∃ candidate, AtPosition secretKey.parameter input candidate ∧ ¬ IsOtsPosition candidate ∧
        ¬ ∀ child ∈ candidate.children, Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache child := by
      rintro ⟨candidate, hc, hn, _⟩
      exact hn (atPosition_unique secretKey.parameter hat hc ▸ hp)
    have hnotProbe : ¬ ∃ probe : FtsSecretProbe, probe.input secretKey.parameter = input := by
      rintro ⟨probe, heq⟩
      have hprobe : AtPosition secretKey.parameter input (.ftsLeaf probe.index probe.tree probe.leafIdx) := by
        rw [← heq]
        exact ⟨digestBytes probe.candidate, rfl⟩
      rw [atPosition_unique secretKey.parameter hat hprobe] at hp
      exact hp
    simp only [otsHashInputCharge, FtsProbeSimulation.ftsHashQueryCharge,
      if_neg hnotProbe, ftsParentQueryCharge, parentReserveCharge, if_neg hnotParent, Nat.cast_zero, add_zero]
    split_ifs <;> norm_num
  · by_cases hprobe : ∃ probe : FtsSecretProbe, probe.input secretKey.parameter = input
    · obtain ⟨probe, heq⟩ := hprobe
      have hat : AtPosition secretKey.parameter input (.ftsLeaf probe.index probe.tree probe.leafIdx) := by
        rw [← heq]
        exact ⟨digestBytes probe.candidate, rfl⟩
      have hnotParent : ¬ ∃ candidate, AtPosition secretKey.parameter input candidate ∧ ¬ IsOtsPosition candidate ∧
          ¬ ∀ child ∈ candidate.children, Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache child := by
        rintro ⟨candidate, hc, _, hn⟩
        have he := atPosition_unique secretKey.parameter hc hat
        subst candidate
        exact hn (by simp [Position.children])
      simp only [otsHashInputCharge, if_neg hots, FtsProbeSimulation.ftsHashQueryCharge,
        ftsParentQueryCharge, parentReserveCharge, if_neg hnotParent, Nat.cast_zero, zero_add, add_zero]
      split_ifs <;> norm_num
    · simp only [otsHashInputCharge, if_neg hots, FtsProbeSimulation.ftsHashQueryCharge, if_neg hprobe,
        ftsParentQueryCharge, parentReserveCharge, zero_add]
      split_ifs <;> norm_num

theorem sampled_ots_ftsLeaf_parent_queryCharge_le (adversary : Adversary)
    (q : Nat) (hq : HasHashQueryBound scheme adversary q) :
    sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary +
      sampledQueryCharge (fun secretKey => FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter) adversary +
      sampledQueryCharge ftsParentQueryCharge adversary ≤ q := by
  rw [← sampledQueryCharge_add, ← sampledQueryCharge_add]
  simpa only [one_mul] using sampledQueryCharge_le_const _ 1 ots_ftsLeaf_parent_queryCharge_le_one adversary q hq

end SphincsSecurity.Concrete

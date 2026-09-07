import SphincsSecurity.Proof.LinearReuseReserve
import SphincsSecurity.Proof.CachedPairReserve

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def cachedLinearReuseReserve (remaining : Nat) (key : SecretKey) (q : Nat)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) : ENNReal :=
  linearReuseReserve (cacheSlotCount q cache) ((2 ^ 176 : Nat) : ENNReal)⁻¹
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * digestReuseWeight q)
    (allMessageTargetReuseCharge remaining key cache log q) (allMessageOccupancyReuseCharge remaining key cache log q)
    (cachedUniformIncrement remaining key cache log)

noncomputable def freshMessageReuseCharge (remaining : Nat) (key : SecretKey) (q : Nat)
    (log : QueryLog SigningSpec) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if cache input = none ∧ MessageHashInput key.parameter input then
    2 * ((cacheSlotCount q cache - 1 : Nat) : ENNReal) *
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * digestReuseWeight q) * ((2 ^ 176 : Nat) : ENNReal)⁻¹ *
      uniformOccupancyIncrement remaining key cache log else 0

theorem cachedLinearReuseReserve_of_no_message (remaining : Nat) (key : SecretKey) (q : Nat)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hnone : ∀ input, MessageHashInput key.parameter input → cache input = none) :
    cachedLinearReuseReserve remaining key q cache log = 0 := by
  simp only [cachedLinearReuseReserve, linearReuseReserve, allMessageTargetReuseCharge, allMessageOccupancyReuseCharge,
    cachedUniformIncrement, cacheMessageWeight_of_no_message key.parameter _ cache hnone, zero_mul, mul_zero, zero_add]

theorem cacheCapacityReuseCharge_le_linearReserve (remaining : Nat) (key : SecretKey) (q : Nat)
    (state : CoverLogState) (message : Message) (hfinite : Finite state.1) :
    cacheCapacityReuseCharge remaining key q state message ≤ cachedLinearReuseReserve remaining key q state.1 state.2 := by
  unfold cacheCapacityReuseCharge cachedLinearReuseReserve linearReuseReserve
  rw [cacheSlotCount_cast q state.1 hfinite]
  have hfirst : allMessageTargetReuseCharge remaining key state.1 state.2 q +
      cacheCapacity q state.1 * (allMessageOccupancyReuseCharge remaining key state.1 state.2 q * ((2 ^ 176 : Nat) : ENNReal)⁻¹) =
      allMessageTargetReuseCharge remaining key state.1 state.2 q +
        cacheCapacity q state.1 * ((2 ^ 176 : Nat) : ENNReal)⁻¹ * allMessageOccupancyReuseCharge remaining key state.1 state.2 q := by ring
  rw [hfirst]
  exact le_self_add

theorem cachedLinearReuseReserve_le_pairReserve (remaining : Nat) (key : SecretKey) (q : Nat)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) :
    cachedLinearReuseReserve remaining key q cache log ≤ cachedPairReuseReserve remaining key q cache log :=
  le_self_add

theorem expected_message_cacheQuery_linearReserve_le (remaining : Nat) (key : SecretKey) (q : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : MessageHashInput key.parameter input) (hcap : QueryCache.enncard before + 1 ≤ q) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      cachedLinearReuseReserve remaining key q (before.cacheQuery input output) log) ≤
      cachedLinearReuseReserve remaining key q before log + freshMessageReuseCharge remaining key q log before input := by
  let slots := cacheSlotCount q (before.cacheQuery input default)
  have hbefore : cacheSlotCount q before = slots + 1 := cacheSlotCount_cacheQuery_succ q before input default hfresh hcap
  have hafter (output : HashOutput) : cacheSlotCount q (before.cacheQuery input output) = slots := by
    have h := cacheSlotCount_cacheQuery_succ q before input output hfresh hcap
    omega
  simp only [cachedLinearReuseReserve, freshMessageReuseCharge, hfresh, hmessage, and_self, if_true, hafter, hbefore, Nat.add_sub_cancel]
  apply expected_linearReuseReserve_le
  · exact expected_allMessageTargetReuseCharge_le_increments remaining key before log input hfresh hsigned hmessage q
  · exact le_of_eq (expected_allMessageOccupancyReuseCharge_eq_increment remaining key before log input hfresh hsigned hmessage q)
  · simpa only [mul_comm] using expected_cachedUniformIncrement_cacheQuery_le remaining key before log input hfresh hsigned hmessage

theorem nonmessage_cacheQuery_linearReserve_le (remaining : Nat) (key : SecretKey) (q : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : ¬ MessageHashInput key.parameter input) (hcap : QueryCache.enncard before + 1 ≤ q) :
    cachedLinearReuseReserve remaining key q (before.cacheQuery input output) log ≤ cachedLinearReuseReserve remaining key q before log := by
  have hslots : cacheSlotCount q (before.cacheQuery input output) ≤ cacheSlotCount q before := by
    rw [cacheSlotCount_cacheQuery_succ q before input output hfresh hcap]
    omega
  simp only [cachedLinearReuseReserve, allMessageTargetReuseCharge_cacheQuery_of_not_message remaining key before log input output hfresh hsigned hmessage q,
    allMessageOccupancyReuseCharge_cacheQuery_of_not_message remaining key before log input output hfresh hsigned hmessage q,
    cachedUniformIncrement_cacheQuery remaining key before log input output hfresh hsigned, hmessage, false_and, if_false, add_zero]
  exact linearReuseReserve_mono_slots hslots _ _ _ _ _

theorem expected_randomOracle_linearReserve_le (remaining : Nat) (key : SecretKey) (q : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : HashInput)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hcap : ∀ result ∈ support ((randomOracle input).run before), QueryCache.enncard result.2 ≤ q) :
    (∑' result, Pr[= result | (randomOracle input).run before] * cachedLinearReuseReserve remaining key q result.2 log) ≤
      cachedLinearReuseReserve remaining key q before log + freshMessageReuseCharge remaining key q log before input := by
  by_cases hfresh : before input = none
  · have hcap' : QueryCache.enncard before + 1 ≤ q := by
      have hdefault : (default : HashOutput) ∈ support ($ᵗ HashOutput : ProbComp HashOutput) := by simp
      have h := hcap (default, before.cacheQuery input default) (by
        rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, support_map]
        exact ⟨default, hdefault, rfl⟩)
      rwa [enncard_cacheQuery_of_fresh before input default hfresh] at h
    rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    by_cases hmessage : MessageHashInput key.parameter input
    · exact expected_message_cacheQuery_linearReserve_le remaining key q before log input hfresh hsigned hmessage hcap'
    · simp only [freshMessageReuseCharge, hmessage, and_false, if_false, add_zero]
      calc
        _ ≤ ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * cachedLinearReuseReserve remaining key q before log :=
          ENNReal.tsum_le_tsum (fun output => mul_le_mul' le_rfl
            (nonmessage_cacheQuery_linearReserve_le remaining key q before log input output hfresh hsigned hmessage hcap'))
        _ ≤ _ := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one
  · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ houtput, tsum_probOutput_pure_mul]
    simp only [freshMessageReuseCharge, hfresh, false_and, if_false, add_zero, le_refl]

end SphincsSecurity.Concrete

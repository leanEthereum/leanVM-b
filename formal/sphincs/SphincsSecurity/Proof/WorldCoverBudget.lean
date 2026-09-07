import SphincsSecurity.Proof.InterleavedMass
import SphincsSecurity.Proof.ValidInterleavedCover

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def frozenCoverWeight (key : SecretKey) (state : CoverLogState) : ENNReal :=
  frozenLogOccupancy key state * ((2 ^ 176 : Nat) : ENNReal)⁻¹

noncomputable def worldInterleavedCoverStepCharge (key : SecretKey) (cap : Nat) (state : CoverLogState) :
    (OracleWorld + SigningSpec).Domain → ENNReal
  | .inl world => validInterleavedCoverStepCharge key cap state (.inl world)
  | .inr _ => 0

theorem worldInterleavedCoverStepCharge_le (key : SecretKey) (cap : Nat) (state : CoverLogState)
    (input : (OracleWorld + SigningSpec).Domain) :
    worldInterleavedCoverStepCharge key cap state input ≤
      (if isDirectHashQuery input then 1 else 0 : Nat) * frozenCoverWeight key state := by
  cases input with
  | inr message => simp only [worldInterleavedCoverStepCharge, isDirectHashQuery, if_false, Nat.cast_zero, zero_mul, le_refl]
  | inl world =>
      cases world with
      | inl uniform =>
          simp [worldInterleavedCoverStepCharge, validInterleavedCoverStepCharge, interleavedCoverStepCharge,
            worldCoverCharge, hashQueryCharge, isDirectHashQuery]
      | inr input =>
          simp only [worldInterleavedCoverStepCharge, isDirectHashQuery, if_true, Nat.cast_one, one_mul]
          by_cases hvalid : ValidSigningStep state.2 (.inl (.inr input))
          · rw [validInterleavedCoverStepCharge, if_pos hvalid]
            by_cases hcap : QueryCache.enncard state.1 ≤ cap
            · rw [interleavedCoverStepCharge, dif_pos hcap]
              apply (worldCoverCharge_le_observedOccupancy key state (.inr input)).trans
              simp only [hashQueryCharge, frozenCoverWeight]
              apply mul_le_mul' ?_ le_rfl
              split_ifs
              · exact le_of_eq (frozenLogOccupancy_of_valid key state hvalid).symm
              · exact bot_le
            · rw [interleavedCoverStepCharge, dif_neg hcap]
              exact bot_le
          · rw [validInterleavedCoverStepCharge, if_neg hvalid]
            exact bot_le

theorem frozenCoverWeight_le_expected_terminal {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    frozenCoverWeight key state ≤ ∑' result,
      Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] * frozenCoverWeight key result.2 := by
  simp only [frozenCoverWeight, ← mul_assoc, ENNReal.tsum_mul_right]
  exact mul_le_mul' (frozenLogOccupancy_le_expected_terminal key computation state hsigned) le_rfl

theorem expanded_query_bound_log_step {α : Type} (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl key) (OracleSpec.query input >>= next)).IsQueryBoundP (· matches Sum.inr _) q)
    (state : CoverLogState) :
    (if isDirectHashQuery input then 1 else 0 : Nat) ≤ q ∧
      ∀ result ∈ support ((logTracedMappedAdversaryImpl key input).run state),
        (simulateQ (expandedAdversaryImpl key) (next result.1)).IsQueryBoundP (· matches Sum.inr _)
          (q - if isDirectHashQuery input then 1 else 0) := by
  cases input with
  | inl world =>
      rw [simulateQ_expandedAdversaryImpl_query_bind_inl, isQueryBoundP_query_bind_iff] at hbound
      cases world with
      | inl uniform =>
          simp only [isDirectHashQuery, if_false, Nat.sub_zero]
          exact ⟨Nat.zero_le _, fun result _ => hbound.2 result.1⟩
      | inr input =>
          simp only [isDirectHashQuery, if_true]
          have hp : 0 < q := by simpa using hbound.1
          exact ⟨Nat.succ_le_iff.mpr hp, fun result _ => hbound.2 result.1⟩
  | inr message =>
      simp only [isDirectHashQuery, if_false, Nat.sub_zero]
      refine ⟨Nat.zero_le _, ?_⟩
      intro result hresult
      rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
      obtain ⟨base, hbase, rfl⟩ := hresult
      have houtput := unloggedMappedAdversaryImpl_output_mem_support_expanded key (.inr message) state.1 base.2 base.1 hbase
      rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
      exact isQueryBoundP_of_bind hbound base.1 houtput

noncomputable def expectedWorldCoverCharge {α : Type} (key : SecretKey) (cap : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : CoverLogState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => worldInterleavedCoverStepCharge key cap state input +
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * next result.1 result.2) computation

@[simp] theorem expectedWorldCoverCharge_pure {α : Type} (key : SecretKey) (cap : Nat)
    (value : α) (state : CoverLogState) : expectedWorldCoverCharge key cap (pure value) state = 0 := rfl

theorem expectedWorldCoverCharge_query_bind {α : Type} (key : SecretKey) (cap : Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (state : CoverLogState) :
    expectedWorldCoverCharge key cap (OracleSpec.query input >>= next) state =
      worldInterleavedCoverStepCharge key cap state input + ∑' result,
        Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * expectedWorldCoverCharge key cap (next result.1) result.2 := by
  cases input <;> rfl

theorem expectedWorldCoverCharge_le_expanded_queryBound {α : Type} (key : SecretKey) (cap : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl key) computation).IsQueryBoundP (· matches Sum.inr _) q)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    expectedWorldCoverCharge key cap computation state ≤
      (q : ENNReal) * ∑' result, Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) computation).run state] *
        frozenCoverWeight key result.2 := by
  induction computation using OracleComp.inductionOn generalizing q state with
  | pure value => exact bot_le
  | query_bind input next ih =>
      let count : Nat := if isDirectHashQuery input then 1 else 0
      let terminal : ENNReal := ∑' result,
        Pr[= result | (simulateQ (logTracedMappedAdversaryImpl key) (OracleSpec.query input >>= next)).run state] *
          frozenCoverWeight key result.2
      obtain ⟨hcount, htailBound⟩ := expanded_query_bound_log_step key input next q hbound state
      have hcurrent : worldInterleavedCoverStepCharge key cap state input ≤ (count : ENNReal) * terminal :=
        (worldInterleavedCoverStepCharge_le key cap state input).trans
          (mul_le_mul' le_rfl (frozenCoverWeight_le_expected_terminal key _ state hsigned))
      have htail : (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
          expectedWorldCoverCharge key cap (next result.1) result.2) ≤ ((q - count : Nat) : ENNReal) * terminal := by
        calc
          _ ≤ ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] *
              (((q - count : Nat) : ENNReal) * ∑' last,
                Pr[= last | (simulateQ (logTracedMappedAdversaryImpl key) (next result.1)).run result.2] *
                  frozenCoverWeight key last.2) := by
            apply ENNReal.tsum_le_tsum
            intro result
            by_cases hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)
            · exact mul_le_mul' le_rfl (ih result.1 (q - count) (htailBound result hresult) result.2
                (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned result hresult))
            · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
          _ = _ := by
            simp_rw [mul_left_comm (Pr[= _ | _])]
            rw [ENNReal.tsum_mul_left]
            dsimp only [terminal]
            rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
      rw [expectedWorldCoverCharge_query_bind]
      apply (add_le_add hcurrent htail).trans_eq
      rw [← add_mul, ← Nat.cast_add, Nat.add_sub_of_le hcount]

end SphincsSecurity.Concrete

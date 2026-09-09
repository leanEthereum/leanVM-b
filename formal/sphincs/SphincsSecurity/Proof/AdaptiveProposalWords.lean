import SphincsSecurity.Proof.ProposalBridgeKernel

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal

noncomputable def proposalEmissionRun {α σ : Type*} (transition : σ → PMF (α × σ)) :
    Nat → σ → PMF (List α × σ)
  | 0, state => pure ([], state)
  | steps + 1, state => (transition state).bind fun result =>
      (proposalEmissionRun transition steps result.2).map (fun final => (result.1 :: final.1, final.2))

theorem proposalEmissionRun_word {α σ : Type*} (base : PMF α) (transition : σ → PMF (α × σ))
    (hlabel : ∀ state, (transition state).map Prod.fst = base) (steps : Nat) (state : σ) :
    (proposalEmissionRun transition steps state).map Prod.fst = independentProposalWord base steps := by
  induction steps generalizing state with
  | zero =>
      change (PMF.pure ([], state)).map Prod.fst = PMF.pure []
      exact PMF.pure_map _ _
  | succ steps ih =>
      rw [proposalEmissionRun, PMF.map_bind]
      have hbranch (result : α × σ) :
          ((proposalEmissionRun transition steps result.2).map
            (fun final => (result.1 :: final.1, final.2))).map Prod.fst =
          (independentProposalWord base steps).map (result.1 :: ·) := by
        calc
          _ = ((proposalEmissionRun transition steps result.2).map Prod.fst).map (result.1 :: ·) := by
            rw [PMF.map_comp, PMF.map_comp]
            rfl
          _ = _ := by rw [ih]
      simp_rw [hbranch]
      change (transition state).bind ((fun head => (independentProposalWord base steps).map (head :: ·)) ∘ Prod.fst) = _
      rw [← PMF.bind_map, hlabel]
      rfl

noncomputable def proposalRecordTransition {α σ Ω : Type*} (base : PMF α) (record : σ → PMF Ω)
    (label : Ω → α) (nextState : σ → Ω → σ) (accept : ENNReal) (hlt : accept < 1)
    (hcap : ∀ state index, accept * ((record state).map label) index ≤ base index) (state : σ) : PMF (α × σ) :=
  (proposalRecordStep base (record state) label accept hlt (hcap state)).map
    (Sum.elim (fun index => (index, state)) (fun outcome => (label outcome, nextState state outcome)))

theorem proposalRecordTransition_label {α σ Ω : Type*} (base : PMF α) (record : σ → PMF Ω)
    (label : Ω → α) (nextState : σ → Ω → σ) (accept : ENNReal) (hlt : accept < 1)
    (hcap : ∀ state index, accept * ((record state).map label) index ≤ base index) (state : σ) :
    (proposalRecordTransition base record label nextState accept hlt hcap state).map Prod.fst = base := by
  rw [proposalRecordTransition, PMF.map_comp]
  have hfun : Prod.fst ∘ Sum.elim (fun index => (index, state)) (fun outcome => (label outcome, nextState state outcome)) =
      Sum.elim id label := by
    funext branch
    cases branch <;> rfl
  rw [hfun]
  exact proposalRecordStep_label base (record state) label accept hlt (hcap state)

theorem adaptiveRecordProposalWord {α σ Ω : Type*} (base : PMF α) (record : σ → PMF Ω)
    (label : Ω → α) (nextState : σ → Ω → σ) (accept : ENNReal) (hlt : accept < 1)
    (hcap : ∀ state index, accept * ((record state).map label) index ≤ base index) (steps : Nat) (state : σ) :
    (proposalEmissionRun (proposalRecordTransition base record label nextState accept hlt hcap) steps state).map Prod.fst =
      independentProposalWord base steps :=
  proposalEmissionRun_word base _ (proposalRecordTransition_label base record label nextState accept hlt hcap) steps state

theorem adaptiveRecordProposalWord_apply {α σ Ω : Type*} (base : PMF α) (record : σ → PMF Ω)
    (label : Ω → α) (nextState : σ → Ω → σ) (accept : ENNReal) (hlt : accept < 1)
    (hcap : ∀ state index, accept * ((record state).map label) index ≤ base index)
    (steps : Nat) (state : σ) (word : List α) :
    ((proposalEmissionRun (proposalRecordTransition base record label nextState accept hlt hcap) steps state).map Prod.fst) word =
      if word.length = steps then (word.map base).prod else 0 := by
  rw [adaptiveRecordProposalWord, independentProposalWord_apply]

theorem evalDist_sampleUniformProposalWord {α : Type} [SampleableType α] [Fintype α] [Nonempty α] (steps : Nat) :
    𝒟[sampleUniformProposalWord α steps] =
      (liftM (independentProposalWord (PMF.uniformOfFintype α) steps) : SPMF (List α)) := by
  induction steps with
  | zero => simp only [sampleUniformProposalWord, independentProposalWord, evalDist_pure]
  | succ steps ih =>
      simp only [sampleUniformProposalWord, evalDist_bind, evalDist_pure, evalDist_uniformSample, ih,
        independentProposalWord, PMF.map, Function.comp_def, ← PMF.monad_bind_eq_bind, PMF.evalDist_eq]
      simp only [← PMF.monad_pure_eq_pure, liftM_pure]

noncomputable def targetProposalAcceptance : ENNReal := targetProposalOverhead⁻¹

theorem targetProposalAcceptance_ne_zero : targetProposalAcceptance ≠ 0 := by
  rw [targetProposalAcceptance, ENNReal.inv_ne_zero]
  unfold targetProposalOverhead
  finiteness

theorem targetProposalAcceptance_lt_one : targetProposalAcceptance < 1 := by
  rw [targetProposalAcceptance, ENNReal.inv_lt_one]
  unfold targetProposalOverhead
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

theorem targetProposalAcceptance_cap {Ω : Type*} (record : PMF Ω) (label : Ω → Index)
    (hbound : ∀ index, (record.map label) index ≤ targetProposalIndexRate) (index : Index) :
    targetProposalAcceptance * (record.map label) index ≤ PMF.uniformOfFintype Index index := by
  rw [PMF.uniformOfFintype_apply, targetProposalAcceptance]
  calc
    _ ≤ targetProposalOverhead⁻¹ * targetProposalIndexRate := mul_le_mul' le_rfl (hbound index)
    _ = _ := by
      have hpositive : 0 < targetProposalOverhead :=
        zero_lt_one.trans (ENNReal.inv_lt_one.mp targetProposalAcceptance_lt_one)
      rw [targetProposalIndexRate, ← mul_assoc,
        ENNReal.inv_mul_cancel hpositive.ne'
          (by unfold targetProposalOverhead; finiteness), one_mul]

noncomputable def indexProposalTransition {σ Ω : Type*} (record : σ → PMF Ω)
    (label : Ω → Index) (nextState : σ → Ω → σ)
    (hbound : ∀ state index, ((record state).map label) index ≤ targetProposalIndexRate) : σ → PMF (Index × σ) :=
  proposalRecordTransition (PMF.uniformOfFintype Index) record label nextState targetProposalAcceptance
    targetProposalAcceptance_lt_one (fun state => targetProposalAcceptance_cap (record state) label (hbound state))

theorem indexProposalWord_evalDist {σ Ω : Type} (record : σ → PMF Ω)
    (label : Ω → Index) (nextState : σ → Ω → σ)
    (hbound : ∀ state index, ((record state).map label) index ≤ targetProposalIndexRate) (steps : Nat) (state : σ) :
    𝒟[(proposalEmissionRun (indexProposalTransition record label nextState hbound) steps state).map Prod.fst] =
      𝒟[sampleUniformProposalWord Index steps] := by
  rw [indexProposalTransition, adaptiveRecordProposalWord, PMF.evalDist_eq, evalDist_sampleUniformProposalWord]

end SphincsSecurity.Concrete

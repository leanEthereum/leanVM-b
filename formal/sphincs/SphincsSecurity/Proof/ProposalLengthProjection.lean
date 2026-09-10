import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.SigningProposalRecord

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

theorem independentProposalWord_length {α : Type*} (law : PMF α) (steps : Nat) :
    (independentProposalWord law steps).map List.length = PMF.pure steps := by
  induction steps with
  | zero => exact PMF.pure_map _ _
  | succ steps ih =>
      rw [independentProposalWord, PMF.map_bind]
      have hbranch (head : α) :
          ((independentProposalWord law steps).map (head :: ·)).map List.length =
            PMF.pure (steps + 1) := by
        calc
          _ = ((independentProposalWord law steps).map List.length).map Nat.succ := by
            rw [PMF.map_comp, PMF.map_comp]
            rfl
          _ = _ := by rw [ih, PMF.pure_map]
      simp_rw [hbranch]
      exact PMF.bind_const _ _

theorem rejectedProposalWord_length {α : Type*} (law : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (rejectedProposalWord law accept hpos hle).map List.length =
      proposalFailureCount accept hpos hle := by
  rw [rejectedProposalWord, PMF.map_bind]
  simp_rw [independentProposalWord_length]
  exact PMF.bind_pure _

noncomputable def proposalBlockLength (accept : ENNReal) (hpos : accept ≠ 0)
    (hle : accept ≤ 1) : PMF Nat :=
  (proposalFailureCount accept hpos hle).map Nat.succ

theorem proposalBlockLength_zero (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    proposalBlockLength accept hpos hle 0 = 0 :=
  pmf_map_apply_zero_of_not_image _ _ _ (fun _ => Nat.zero_ne_add_one _)

theorem proposalBlockLength_succ (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1)
    (failures : Nat) :
    proposalBlockLength accept hpos hle (failures + 1) = accept * (1 - accept) ^ failures :=
  (pmf_map_injective_apply _ _ Nat.succ_injective failures).trans rfl

theorem rejectedProposalWord_blockLength {α : Type*} (law : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (rejectedProposalWord law accept hpos hle).map (fun word => word.length + 1) =
      proposalBlockLength accept hpos hle := by
  change _ = ((proposalFailureCount accept hpos hle).map Nat.succ)
  rw [← rejectedProposalWord_length law accept hpos hle, PMF.map_comp]
  rfl

noncomputable def recordLengthBridge {Ω : Type*} (record : PMF Ω)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) : PMF (Nat × Ω) :=
  record.bind fun outcome =>
    (proposalBlockLength accept hpos hle).map (fun length => (length, outcome))

theorem recordProposalBridge_length_record {α Ω : Type*} (record : PMF Ω) (rejected : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (recordProposalBridge record rejected accept hpos hle).map
      (fun result => (result.1.length + 1, result.2)) = recordLengthBridge record accept hpos hle := by
  rw [recordProposalBridge, PMF.map_bind]
  have hbranch (outcome : Ω) :
      ((rejectedProposalWord rejected accept hpos hle).map (fun word => (word, outcome))).map
        (fun result => (result.1.length + 1, result.2)) =
      (proposalBlockLength accept hpos hle).map (fun length => (length, outcome)) := by
    rw [← rejectedProposalWord_blockLength rejected accept hpos hle, PMF.map_comp, PMF.map_comp]
    rfl
  simp_rw [hbranch]
  rfl

theorem recordLengthBridge_map_record {Ω Ξ : Type*} (record : PMF Ω)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (observe : Ω → Ξ) :
    (recordLengthBridge record accept hpos hle).map (fun result => (result.1, observe result.2)) =
      recordLengthBridge (record.map observe) accept hpos hle := by
  simp only [recordLengthBridge, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]

theorem recordLengthBridge_record {Ω : Type*} (record : PMF Ω)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (recordLengthBridge record accept hpos hle).map Prod.snd = record := by
  rw [recordLengthBridge, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (record.bind fun outcome =>
    (proposalBlockLength accept hpos hle).map (Function.const Nat outcome)) = record
  simp only [PMF.map_const, PMF.bind_pure]

theorem recordLengthBridge_length {Ω : Type*} (record : PMF Ω)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (recordLengthBridge record accept hpos hle).map Prod.fst = proposalBlockLength accept hpos hle := by
  rw [recordLengthBridge, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (record.bind fun _ => (proposalBlockLength accept hpos hle).map id) = _
  rw [PMF.map_id, PMF.bind_const]

theorem recordLengthBridge_apply {Ω : Type*} (record : PMF Ω)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (length : Nat) (outcome : Ω) :
    recordLengthBridge record accept hpos hle (length, outcome) =
      record outcome * proposalBlockLength accept hpos hle length := by
  classical
  letI : DecidableEq Ω := Classical.decEq Ω
  rw [recordLengthBridge, PMF.bind_apply]
  have hm (value : Ω) :
      ((proposalBlockLength accept hpos hle).map (fun length => (length, value))) (length, outcome) =
        if outcome = value then proposalBlockLength accept hpos hle length else 0 := by
    by_cases h : outcome = value
    · subst outcome
      rw [if_pos rfl]
      exact pmf_map_injective_apply _ _ (fun _ _ h => (Prod.mk.inj h).1) length
    · rw [if_neg h]
      exact pmf_map_apply_zero_of_not_image _ _ _ (fun _ heq => h (Prod.mk.inj heq).2)
  simp only [hm, mul_ite, mul_zero, tsum_ite_eq']

theorem recordLengthBridge_bind {σ Ω : Type*} (prior : PMF σ) (record : σ → PMF Ω)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    prior.bind (fun state => (recordLengthBridge (record state) accept hpos hle).map
      (fun result => (result.1, (state, result.2)))) =
    recordLengthBridge (prior.bind fun state => (record state).map (fun outcome => (state, outcome)))
      accept hpos hle := by
  simp only [recordLengthBridge, PMF.map_bind, PMF.bind_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]

theorem signingProposalBridge_length_completed_record {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (spent : Nat)
    (hbound : ProposalCacheBound key cache spent) :
    (signingProposalBridge trace key message cache spent hbound).map
      (fun result => (result.1.length + 1, result.2)) =
    recordLengthBridge (completedSigningRecord trace key message cache)
      targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le := by
  unfold signingProposalBridge cappedRecordProposalBridge
  exact recordProposalBridge_length_record _ _ _ _ _

theorem signingProposalBridge_length_record {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (spent : Nat)
    (hbound : ProposalCacheBound key cache spent) :
    (signingProposalBridge trace key message cache spent hbound).map
      (fun result => (result.1.length + 1, result.2.1)) =
    recordLengthBridge (liftM (tracedSigningRun trace key message cache) : PMF (TracedSigningRecord ω))
      targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le := by
  calc
    _ = ((signingProposalBridge trace key message cache spent hbound).map
        (fun result => (result.1.length + 1, result.2))).map (fun result => (result.1, result.2.1)) :=
      (PMF.map_comp _ _ _).symm
    _ = _ := by
      rw [signingProposalBridge_length_completed_record, recordLengthBridge_map_record,
        completedSigningRecord_forget]

theorem signingProposalBridge_length_original_record {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (spent : Nat)
    (hbound : ProposalCacheBound key cache spent) :
    (signingProposalBridge trace key message cache spent hbound).map
      (fun result => (result.1.length + 1, signingRecordResponse result.2.1)) =
    recordLengthBridge
      (liftM (((simulateQ (romImpl.withTrace trace) (sign key message)).run).run cache) :
        PMF ((Option Signature × ω) × QueryCache HashSpec))
      targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le := by
  calc
    _ = ((signingProposalBridge trace key message cache spent hbound).map
        (fun result => (result.1.length + 1, result.2.1))).map
          (fun result => (result.1, signingRecordResponse result.2)) := (PMF.map_comp _ _ _).symm
    _ = _ := by
      have hrecord :
          (liftM (tracedSigningRun trace key message cache) : PMF (TracedSigningRecord ω)).map
            signingRecordResponse =
          (liftM (signingRecordResponse <$> tracedSigningRun trace key message cache) :
            PMF ((Option Signature × ω) × QueryCache HashSpec)) :=
        (liftM_map (m := ProbComp) (n := PMF) _ _).symm
      rw [signingProposalBridge_length_record, recordLengthBridge_map_record, hrecord,
        tracedSigningRun_signature]

theorem signingProposalBridge_length_boundary_record
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (spent : Nat)
    (hbound : ProposalCacheBound key cache spent) :
    (signingProposalBridge (signingBoundaryTrace key.parameter) key message cache spent hbound).map
      (fun result => (result.1.length + 1, (signingRecordResponse result.2.1).1)) =
    recordLengthBridge
      ((liftM (((simulateQ (romImpl.withTrace (signingBoundaryTrace key.parameter))
        (sign key message)).run).run cache) :
          PMF ((Option Signature × SigningBoundaryTrace) × QueryCache HashSpec)).map Prod.fst)
      targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le := by
  calc
    _ = ((signingProposalBridge (signingBoundaryTrace key.parameter) key message cache spent hbound).map
        (fun result => (result.1.length + 1, signingRecordResponse result.2.1))).map
          (fun result => (result.1, result.2.1)) := (PMF.map_comp _ _ _).symm
    _ = _ := by rw [signingProposalBridge_length_original_record, recordLengthBridge_map_record]

end SphincsSecurity.Concrete

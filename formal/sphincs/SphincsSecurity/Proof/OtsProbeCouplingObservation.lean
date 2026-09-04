import SphincsSecurity.Proof.OtsProbeJointSnapshotErasure
import VCVio.ProgramLogic.Relational.Quantitative

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

/-- A comparison of an observation can retain the complete sampled output. -/
theorem relTriple_lift_left_observation
    {left : ProbComp α} {right : ProbComp β} (observe : α → β)
    {relation : β → β → Prop}
    (h : RelTriple (observe <$> left) right relation) :
    RelTriple left right (fun a b => relation (observe a) b) := by
  classical
  obtain ⟨coupling, hcoupling⟩ := relTriple_iff_relWP.1 h
  refine relTriple_iff_relWP.2
    ⟨⟨liftLeftMapCoupling observe coupling,
      liftLeftMapCoupling_isCoupling observe coupling⟩, ?_⟩
  intro pair hpair
  change pair ∈ support (liftLeftMapCoupling observe coupling) at hpair
  unfold liftLeftMapCoupling at hpair
  rw [mem_support_bind_iff] at hpair
  obtain ⟨observed, hobserved, hpair⟩ := hpair
  rw [support_map] at hpair
  obtain ⟨value, hvalue, hpair⟩ := hpair
  subst pair
  have hsupport : observed.1 ∈ support (evalDist (observe <$> left)) := by
    rw [← coupling.2.map_fst, support_map]
    exact ⟨observed, hobserved, rfl⟩
  let distribution := MonadHom.ofLift _ PMF left
  rw [evalDist_map, support_map] at hsupport
  obtain ⟨original, horiginal, hmap⟩ := hsupport
  change original ∈ (liftM distribution : SPMF α).support at horiginal
  rw [SPMF.support_liftM] at horiginal
  have hex : ∃ a ∈ {a | observe a = observed.1}, a ∈ distribution.support :=
    ⟨original, hmap, horiginal⟩
  have hvalue' : value ∈ (PMF.condOnMap distribution observe observed.1).support := by
    change value ∈ (liftM (PMF.condOnMap distribution observe observed.1) : SPMF α).support at hvalue
    rwa [SPMF.support_liftM] at hvalue
  have hmatch : observe value = observed.1 := by
    by_contra hne
    have hzero := PMF.condOnMap_apply_of_not_mem_fiber distribution observe observed.1 hne hex
    exact ((PMF.mem_support_iff _ _).1 hvalue') hzero
  simpa [hmatch] using hcoupling observed hobserved

theorem relTriple_lift_right_observation
    {left : ProbComp β} {right : ProbComp α} (observe : α → β)
    {relation : β → β → Prop}
    (h : RelTriple left (observe <$> right) relation) :
    RelTriple left right (fun a b => relation a (observe b)) :=
  relTriple_symm (relTriple_lift_left_observation observe (relTriple_symm h))

end SphincsSecurity.Concrete.OtsProbeSimulation

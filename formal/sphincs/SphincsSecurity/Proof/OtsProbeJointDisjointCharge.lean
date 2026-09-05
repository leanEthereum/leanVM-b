import SphincsSecurity.Proof.OtsProbeCombinedCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] sampledGranularAllCanonicalBoundaryWitnessSnapshot
  sampledObservedMaterializedDiagnostic granularAllCanonicalBoundaryWitnessSnapshot
  observedMaterializedRetainedRunFromTable sampledActualRetainedOtsHashTable

set_option maxRecDepth 100000

theorem probEvent_coupling_fst {α β : Type} (left : ProbComp α) (right : ProbComp β)
    (law : SPMF (α × β)) (h : SPMF.IsCoupling law (evalDist left) (evalDist right)) (event : α → Prop) :
    Pr[fun pair => event pair.1 | law] = Pr[event | left] := by
  calc
    _ = Pr[event | Prod.fst <$> law] := (probEvent_map law Prod.fst event).symm
    _ = Pr[event | evalDist left] := congrArg (fun distribution : SPMF α => probEvent distribution event) h.map_fst
    _ = _ := rfl

theorem probEvent_coupling_snd {α β : Type} (left : ProbComp α) (right : ProbComp β)
    (law : SPMF (α × β)) (h : SPMF.IsCoupling law (evalDist left) (evalDist right)) (event : β → Prop) :
    Pr[fun pair => event pair.2 | law] = Pr[event | right] := by
  calc
    _ = Pr[event | Prod.snd <$> law] := (probEvent_map law Prod.snd event).symm
    _ = Pr[event | evalDist right] := congrArg (fun distribution : SPMF β => probEvent distribution event) h.map_snd
    _ = _ := rfl

abbrev BoundaryDiagnosticPair := BoundaryWitnessSnapshotOutput ×
  ObservedMaterializedDiagnostic (RetainedGameResult × SplitHashCache)

structure BoundaryDiagnosticCoupling (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat) where
  law : SPMF BoundaryDiagnosticPair
  marginals : SPMF.IsCoupling law
    (evalDist (sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q))
    (evalDist (sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)))
  aligned : ∀ (pair : BoundaryDiagnosticPair), pair ∈ support law → ∃ table,
    BoundarySnapshotDiagnosticRel table pair.1 pair.2 ∧
      pair.1 ∈ support (granularAllCanonicalBoundaryWitnessSnapshot adversary parameter table ftsSecret q) ∧
      pair.2 ∈ support (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table >>=
        finishObservedMaterializedDiagnostic table)

set_option maxRecDepth 100000 in
noncomputable def boundaryDiagnosticCoupling
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ (SphincsSecurity.expandedAdversaryImpl
        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q) :
    BoundaryDiagnosticCoupling adversary parameter ftsSecret q := by
  have hrel : RelTriple
      (sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q)
      (sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q))
      (fun source diagnostic => ∃ table, BoundarySnapshotDiagnosticRel table source diagnostic ∧
        source ∈ support (granularAllCanonicalBoundaryWitnessSnapshot adversary parameter table ftsSecret q) ∧
        diagnostic ∈ support (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table >>=
          finishObservedMaterializedDiagnostic table)) := by
    unfold sampledGranularAllCanonicalBoundaryWitnessSnapshot sampledObservedMaterializedDiagnostic
    apply relTriple_bind (relTriple_refl sampleOtsHashTable)
    intro leftTable rightTable heq
    subst rightTable
    have hbase := relTriple_granularAllJointSnapshot_diagnostic adversary parameter ftsSecret q leftTable (hbound leftTable)
    have hleft := FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => result ∈ support
        (granularAllCanonicalBoundaryWitnessSnapshot adversary parameter leftTable ftsSecret q))
      (fun _ hresult => hresult)
    apply relTriple_post_mono (FtsProbeSimulation.relTriple_and_right_support hleft)
    intro source diagnostic hfacts
    exact ⟨leftTable, hfacts.1.1, hfacts.1.2, hfacts.2⟩
  exact ⟨(relTriple_iff_relWP.1 hrel).choose.val, (relTriple_iff_relWP.1 hrel).choose.property,
    (relTriple_iff_relWP.1 hrel).choose_spec⟩

namespace BoundaryDiagnosticCoupling

variable {adversary : Adversary} {parameter : PublicParameter}
  {ftsSecret : Index → FtsTree → FtsLeaf → Digest} {q : Nat}
  (joint : BoundaryDiagnosticCoupling adversary parameter ftsSecret q)

theorem probEvent_source (event : BoundaryWitnessSnapshotOutput → Prop) :
    Pr[fun pair => event pair.1 | joint.law] =
      Pr[event | sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q] := by
  exact probEvent_coupling_fst _ _ joint.law joint.marginals event

theorem probEvent_diagnostic (event : ObservedMaterializedDiagnostic (RetainedGameResult × SplitHashCache) → Prop) :
    Pr[fun pair => event pair.2 | joint.law] =
      Pr[event | sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] := by
  exact probEvent_coupling_snd _ _ joint.law joint.marginals event

theorem source_mem_support (pair : BoundaryDiagnosticPair) (hpair : pair ∈ support joint.law) :
    pair.1 ∈ support (sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q) := by
  apply (mem_support_iff_evalDist_apply_ne_zero _ _).2
  apply (SPMF.mem_support_iff _ _).1
  rw [← joint.marginals.map_fst]
  change pair.1 ∈ support (Prod.fst <$> joint.law)
  rw [support_map]
  exact ⟨pair, hpair, rfl⟩

theorem diagnostic_mem_support (pair : BoundaryDiagnosticPair) (hpair : pair ∈ support joint.law) :
    pair.2 ∈ support (sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)) := by
  apply (mem_support_iff_evalDist_apply_ne_zero _ _).2
  apply (SPMF.mem_support_iff _ _).1
  rw [← joint.marginals.map_snd]
  change pair.2 ∈ support (Prod.snd <$> joint.law)
  rw [support_map]
  exact ⟨pair, hpair, rfl⟩

def OrdinaryFailure (pair : BoundaryDiagnosticPair) : Prop :=
  pair.1.outcome.failed = true ∧ pair.2.final = none

def HiddenFailure (pair : BoundaryDiagnosticPair) : Prop :=
  pair.1.outcome.failed = true ∧ pair.2.SuccessfulDoomed

def ResidualFailure (pair : BoundaryDiagnosticPair) : Prop :=
  pair.1.outcome.failed = true ∧ ¬pair.2.Bad

theorem residualFailure_has_witness (pair : BoundaryDiagnosticPair)
    (hpair : pair ∈ support joint.law) (hresidual : ResidualFailure pair) :
    JointSnapshotResidual pair.1 := by
  obtain ⟨table, hrelation, _, _⟩ := joint.aligned pair hpair
  rcases hrelation.failure_classification adversary parameter ftsSecret q table pair.1 pair.2
    (joint.source_mem_support pair hpair) (joint.diagnostic_mem_support pair hpair) with hbad | hwitness
  · exact (hresidual.2 hbad).elim
  · exact hwitness hresidual.1

theorem ordinary_hidden_disjoint (pair : BoundaryDiagnosticPair) :
    ¬(OrdinaryFailure pair ∧ HiddenFailure pair) := by
  rintro ⟨⟨_, hnone⟩, _, hsome, _⟩
  simp [hnone] at hsome

theorem ordinary_residual_disjoint (pair : BoundaryDiagnosticPair) :
    ¬(OrdinaryFailure pair ∧ ResidualFailure pair) := by
  rintro ⟨⟨_, hnone⟩, _, hclean⟩
  exact hclean (Or.inl hnone)

theorem hidden_residual_disjoint (pair : BoundaryDiagnosticPair) :
    ¬(HiddenFailure pair ∧ ResidualFailure pair) := by
  rintro ⟨⟨_, _, hdoomed⟩, _, hclean⟩
  exact hclean (Or.inr hdoomed)

theorem probEvent_failed_eq_disjoint_sum :
    Pr[fun source => source.outcome.failed = true |
      sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q] =
      Pr[OrdinaryFailure | joint.law] + Pr[HiddenFailure | joint.law] +
        Pr[ResidualFailure | joint.law] := by
  classical
  rw [← joint.probEvent_source]
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro pair
  by_cases hfailed : pair.1.outcome.failed = true
  · cases hfinal : pair.2.final with
    | none => simp [OrdinaryFailure, HiddenFailure, ResidualFailure,
        ObservedMaterializedDiagnostic.SuccessfulDoomed, ObservedMaterializedDiagnostic.Bad, hfailed, hfinal]
    | some result =>
        by_cases hdoomed : pair.2.wasDoomed = true <;>
          simp [OrdinaryFailure, HiddenFailure, ResidualFailure,
            ObservedMaterializedDiagnostic.SuccessfulDoomed, ObservedMaterializedDiagnostic.Bad, hfailed, hfinal, hdoomed]
  · simp [OrdinaryFailure, HiddenFailure, ResidualFailure, hfailed]

theorem probEvent_residualFailure_le :
    Pr[ResidualFailure | joint.law] ≤
      Pr[JointSnapshotResidual |
        sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret q] := by
  rw [← joint.probEvent_source]
  exact probEvent_mono (joint.residualFailure_has_witness)

theorem probEvent_verifyProbe_le_disjoint_sum :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
      Pr[OrdinaryFailure | joint.law] + Pr[HiddenFailure | joint.law] +
        Pr[ResidualFailure | joint.law] := by
  rw [← joint.probEvent_failed_eq_disjoint_sum]
  exact probEvent_sampledActualRetained_verifyProbe_le_jointBoundaryFailed adversary parameter ftsSecret q

end BoundaryDiagnosticCoupling

end SphincsSecurity.Concrete.OtsProbeSimulation

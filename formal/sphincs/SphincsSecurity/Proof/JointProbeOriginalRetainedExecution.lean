import SphincsSecurity.Proof.JointProbeOriginalInitialization
import SphincsSecurity.Proof.OuterHashQueryCapBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def runRetained
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : SPMF (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) :=
  initializeRoot parameter otsTable ftsTable q fuel >>= fun initial =>
    run exception parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q)
      initial.1 initial.2.2 false

theorem runRetained_original
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    Prod.snd <$> runRetained exception adversary parameter otsTable ftsTable q fuel =
      evalDist (originalRoot parameter otsTable >>= fun initial => runExceptionMonitor exception
        (simulateQ (expandedAdversaryImpl (secretKey parameter initial.1 otsTable ftsTable))
          (retainedComputation adversary parameter initial.1 q)) initial.2 false) := by
  rw [runRetained, map_bind]
  simp_rw [run_original]
  rw [evalDist_bind, ← initializeRoot_original parameter otsTable ftsTable q fuel, bind_map_left]

noncomputable def originalCappedRetained
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) : ProbComp (Option RetainedGameResult × QueryCache HashSpec) :=
  originalRoot parameter otsTable >>= fun initial =>
    (simulateQ romImpl (simulateQ (expandedAdversaryImpl (secretKey parameter initial.1 otsTable ftsTable))
      (retainedComputation adversary parameter initial.1 q))).run initial.2

theorem runRetained_originalCapped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    (fun pair => pair.2.1) <$> runRetained exception adversary parameter otsTable ftsTable q fuel =
      evalDist (originalCappedRetained adversary parameter otsTable ftsTable q) := by
  have hmap : (fun pair => pair.2.1) <$> runRetained exception adversary parameter otsTable ftsTable q fuel =
      Prod.fst <$> (Prod.snd <$> runRetained exception adversary parameter otsTable ftsTable q fuel) := by rw [Functor.map_map]
  rw [hmap, runRetained_original, ← evalDist_map, map_bind]
  simp_rw [runExceptionMonitor_project]
  rfl

theorem originalCappedRetained_eq_actual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) :
    originalCappedRetained adversary parameter otsTable ftsTable q =
      (fun actual => (some actual.1, actual.2)) <$>
        OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter
          (fun index tree leaf => ftsTable (index, tree, leaf)) (OtsProbeSimulation.extendStartTable otsTable) := by
  rw [originalCappedRetained, OtsProbeSimulation.actualRetainedGameAfterTable, map_bind, originalRoot, simulateQ_romImpl_liftM]
  apply bind_congr
  rintro ⟨root, cache⟩
  dsimp only
  have hcap := OtsProbeSimulation.simulateQ_expandedRetained_capOuterHashQueries adversary q hq parameter hparameter otsTable
    (fun index tree leaf => ftsTable (index, tree, leaf)) hfts root
  change simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) _ =
    some <$> simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) _ at hcap
  rw [retainedComputation, simulateQ_map]
  change (simulateQ romImpl ((Option.map (fun rest => (root, rest))) <$>
    simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable))
      (OtsProbeSimulation.capOuterHashQueries (OtsProbeSimulation.retainedGameRestComputation adversary ⟨root, parameter⟩) q))).run cache = _
  rw [hcap]
  simp only [simulateQ_map, StateT.run_map, bind_pure_comp,
    OtsProbeSimulation.simulateQ_unloggedMapped_eq_expanded, Functor.map_map]
  rfl

theorem runRetained_originalActual
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    (fun pair => pair.2.1) <$> runRetained exception adversary parameter otsTable ftsTable q fuel =
      (fun actual => (some actual.1, actual.2)) <$>
        evalDist (OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter
          (fun index tree leaf => ftsTable (index, tree, leaf)) (OtsProbeSimulation.extendStartTable otsTable)) := by
  rw [runRetained_originalCapped, originalCappedRetained_eq_actual adversary q hq parameter hparameter otsTable ftsTable hfts, evalDist_map]

theorem runRetained_no_ftsWitness
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (pair) (hpair : pair ∈ support (runRetained exception adversary parameter otsTable ftsTable q fuel))
    (finalFrame : Frame) (hframe : pair.1 = some finalFrame) :
    ¬ JointSourceFtsWitness parameter ftsTable (pair.2.1.1, finalFrame.cache) := by
  rw [runRetained, mem_support_bind_iff] at hpair
  obtain ⟨initial, hinitial, hrest⟩ := hpair
  cases hf : initial.1 with
  | none =>
      rw [hf, run_none, support_map] at hrest
      obtain ⟨result, _, rfl⟩ := hrest
      contradiction
  | some frame =>
      have hv := initializeRoot_valid parameter otsTable ftsTable q fuel initial hinitial frame hf
      rw [hf] at hrest
      exact run_retained_no_ftsWitness exception adversary parameter initial.2.1 otsTable ftsTable q fuel frame initial.2.2 false
        hots hv.1 hv.2 pair hrest finalFrame hframe

theorem runRetained_uncoveredFtsSecret_imp_stopped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (pair) (hpair : pair ∈ support (runRetained exception adversary parameter otsTable ftsTable q fuel))
    (actual : RetainedGameResult × QueryCache HashSpec)
    (hactual : actual ∈ support (OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter
      (fun index tree leaf => ftsTable (index, tree, leaf)) (OtsProbeSimulation.extendStartTable otsTable)))
    (hvalue : pair.2.1.1 = some actual.1) (hcache : pair.2.1.2 = actual.2)
    (hwitness : RetainedUncoveredFtsSecretWitness parameter
      (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)) ftsTable actual) :
    pair.1 = none := by
  rw [runRetained, mem_support_bind_iff] at hpair
  obtain ⟨initial, hinitial, hrest⟩ := hpair
  cases hf : initial.1 with
  | none =>
      rw [hf, run_none, support_map] at hrest
      obtain ⟨result, _, rfl⟩ := hrest
      rfl
  | some frame =>
      have hv := initializeRoot_valid parameter otsTable ftsTable q fuel initial hinitial frame hf
      rw [hf] at hrest
      exact run_retained_uncoveredFtsSecret_imp_stopped exception adversary parameter initial.2.1 otsTable ftsTable q fuel frame initial.2.2
        hots hv.1 hv.2 pair hrest actual hactual hvalue hcache hwitness

theorem probEvent_actual_uncoveredFtsSecret_le_runRetained_stopped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[RetainedUncoveredFtsSecretWitness parameter
        (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)) ftsTable |
      OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter
        (fun index tree leaf => ftsTable (index, tree, leaf)) (OtsProbeSimulation.extendStartTable otsTable)] ≤
      Pr[fun pair => pair.1 = none | runRetained exception adversary parameter otsTable ftsTable q fuel] := by
  let witness := RetainedUncoveredFtsSecretWitness parameter
    (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)) ftsTable
  let event : Option RetainedGameResult × QueryCache HashSpec → Prop := fun result =>
    match result.1 with
    | none => False
    | some value => witness (value, result.2)
  have hm := runRetained_originalActual exception adversary q hq parameter hparameter otsTable ftsTable hfts fuel
  have hp := congrArg (fun computation : SPMF (Option RetainedGameResult × QueryCache HashSpec) => Pr[event | computation]) hm
  simp only [probEvent_map, Function.comp_def] at hp
  change Pr[fun pair => event pair.2.1 | runRetained exception adversary parameter otsTable ftsTable q fuel] =
    Pr[witness | OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter
      (fun index tree leaf => ftsTable (index, tree, leaf)) (OtsProbeSimulation.extendStartTable otsTable)] at hp
  rw [← hp]
  apply probEvent_mono
  intro pair hpair hevent
  have hproject : pair.2.1 ∈ support ((fun actual => (some actual.1, actual.2)) <$>
      evalDist (OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter
        (fun index tree leaf => ftsTable (index, tree, leaf)) (OtsProbeSimulation.extendStartTable otsTable))) := by
    rw [← hm, support_map]
    exact ⟨pair, hpair, rfl⟩
  rw [support_map] at hproject
  obtain ⟨actual, hactual, heq⟩ := hproject
  have ha : actual ∈ support (OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter
      (fun index tree leaf => ftsTable (index, tree, leaf)) (OtsProbeSimulation.extendStartTable otsTable)) :=
    (mem_support_iff_evalDist_apply_ne_zero _ _).2 ((SPMF.mem_support_iff _ _).1 hactual)
  have hv : pair.2.1.1 = some actual.1 := (congrArg Prod.fst heq).symm
  have hc : pair.2.1.2 = actual.2 := (congrArg Prod.snd heq).symm
  have hw : witness actual := by
    change event pair.2.1 at hevent
    rw [← heq] at hevent
    exact hevent
  exact runRetained_uncoveredFtsSecret_imp_stopped exception adversary parameter otsTable ftsTable q fuel hots
    pair hpair actual ha hv hc hw

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

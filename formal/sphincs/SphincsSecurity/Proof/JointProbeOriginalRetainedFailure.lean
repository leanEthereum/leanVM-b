import SphincsSecurity.Proof.JointProbeOriginalFailureMonitor

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def runRetainedWithFailure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : SPMF ((Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool) :=
  initializeRoot parameter otsTable ftsTable q fuel >>= fun initial =>
    runWithFailure exception parameter initial.2.1 otsTable ftsTable (retainedComputation adversary parameter initial.2.1 q)
      initial.1 initial.2.2 false initial.1.isNone

theorem runRetainedWithFailure_project
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    Prod.fst <$> runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel =
      runRetained exception adversary parameter otsTable ftsTable q fuel := by
  rw [runRetainedWithFailure, map_bind, runRetained]
  simp_rw [runWithFailure_project]

theorem runRetainedWithFailure_support_project
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) (result)
    (hresult : result ∈ support (runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel)) :
    result.1 ∈ support (runRetained exception adversary parameter otsTable ftsTable q fuel) := by
  rw [← runRetainedWithFailure_project exception adversary parameter otsTable ftsTable q fuel, support_map]
  exact ⟨result, hresult, rfl⟩

theorem runRetainedWithFailure_missing_iff
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) (result)
    (hresult : result ∈ support (runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel)) :
    result.1.1 = none ↔ result.1.2.2 = true ∨ result.2 = true := by
  rw [runRetainedWithFailure, mem_support_bind_iff] at hresult
  obtain ⟨initial, hinitial, hrest⟩ := hresult
  have hvalid : ∀ live, initial.1 = some live → live.Valid parameter otsTable ftsTable initial.2.2 :=
    fun live hlive => (initializeRoot_valid parameter otsTable ftsTable q fuel initial hinitial live hlive).2
  have hbound : ∀ live, initial.1 = some live →
      (retainedComputation adversary parameter initial.2.1 q).IsQueryBoundP OtsProbeSimulation.IsOuterHash live.ftsFuel := by
    intro live hlive
    rw [(initializeRoot_valid parameter otsTable ftsTable q fuel initial hinitial live hlive).1.1]
    exact retainedComputation_hashBound adversary parameter initial.2.1 q
  have hs := runWithFailure_invariant exception parameter initial.2.1 otsTable ftsTable _ initial.1 initial.2.2 false initial.1.isNone
    hvalid hbound rfl result hrest
  have heq := congrArg (fun flag => flag = true) hs.2
  simpa only [Option.isNone_iff_eq_none, Bool.or_eq_true_iff] using heq.to_iff

noncomputable def monitoredRetained
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q : Nat) : ProbComp ((Option RetainedGameResult × QueryCache HashSpec) × Bool) :=
  originalRoot parameter otsTable >>= fun initial => runExceptionMonitor exception
    (simulateQ (expandedAdversaryImpl (secretKey parameter initial.1 otsTable ftsTable))
      (retainedComputation adversary parameter initial.1 q)) initial.2 false

theorem runRetainedWithFailure_original
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    (fun result => result.1.2) <$> runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel =
      evalDist (monitoredRetained exception adversary parameter otsTable ftsTable q) := by
  have hm : (fun result => result.1.2) <$> runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel =
      Prod.snd <$> (Prod.fst <$> runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel) := by rw [Functor.map_map]
  rw [hm, runRetainedWithFailure_project, runRetained_original]
  rfl

def CleanFtsWitness (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option RetainedGameResult × QueryCache HashSpec) × Bool) : Prop :=
  result.2 = false ∧ ∃ value, result.1.1 = some value ∧
    RetainedUncoveredFtsSecretWitness parameter
      (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)) ftsTable (value, result.1.2)

theorem runRetainedWithFailure_clean_ftsWitness_imp_failure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat)
    (result) (hresult : result ∈ support (runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel))
    (hwitness : CleanFtsWitness parameter otsTable ftsTable result.1.2) : result.2 = true := by
  have hproject := runRetainedWithFailure_support_project exception adversary parameter otsTable ftsTable q fuel result hresult
  have hm := runRetained_originalActual exception adversary q hq parameter hparameter otsTable ftsTable hfts fuel
  have hactualMap : result.1.2.1 ∈ support ((fun actual => (some actual.1, actual.2)) <$>
      evalDist (OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter
        (fun index tree leaf => ftsTable (index, tree, leaf)) (OtsProbeSimulation.extendStartTable otsTable))) := by
    rw [← hm, support_map]
    exact ⟨result.1, hproject, rfl⟩
  rw [support_map] at hactualMap
  obtain ⟨actual, hactual, heq⟩ := hactualMap
  have ha : actual ∈ support (OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter
      (fun index tree leaf => ftsTable (index, tree, leaf)) (OtsProbeSimulation.extendStartTable otsTable)) :=
    (mem_support_iff_evalDist_apply_ne_zero _ _).2 ((SPMF.mem_support_iff _ _).1 hactual)
  have hv : result.1.2.1.1 = some actual.1 := (congrArg Prod.fst heq).symm
  have hc : result.1.2.1.2 = actual.2 := (congrArg Prod.snd heq).symm
  obtain ⟨hclean, value, hvalue, hwitness⟩ := hwitness
  have he : value = actual.1 := Option.some.inj (hvalue.symm.trans hv)
  rw [he, hc] at hwitness
  have hnone := runRetained_uncoveredFtsSecret_imp_stopped exception adversary parameter otsTable ftsTable q fuel hots
    result.1 hproject actual ha hv hc hwitness
  have hcause := (runRetainedWithFailure_missing_iff exception adversary parameter otsTable ftsTable q fuel result hresult).1 hnone
  exact hcause.resolve_left (by simp [hclean])

theorem probEvent_original_clean_ftsWitness_le_sharedFailure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[CleanFtsWitness parameter otsTable ftsTable | monitoredRetained exception adversary parameter otsTable ftsTable q] ≤
      Pr[fun result => result.2 = true | runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel] := by
  have hp := congrArg (fun computation => Pr[CleanFtsWitness parameter otsTable ftsTable | computation])
    (runRetainedWithFailure_original exception adversary parameter otsTable ftsTable q fuel)
  simp only [probEvent_map, Function.comp_def] at hp
  change Pr[fun result => CleanFtsWitness parameter otsTable ftsTable result.1.2 |
      runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel] =
    Pr[CleanFtsWitness parameter otsTable ftsTable | monitoredRetained exception adversary parameter otsTable ftsTable q] at hp
  rw [← hp]
  apply probEvent_mono
  intro result hresult hwitness
  exact runRetainedWithFailure_clean_ftsWitness_imp_failure exception adversary q hq parameter hparameter otsTable hots ftsTable hfts fuel
    result hresult hwitness

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

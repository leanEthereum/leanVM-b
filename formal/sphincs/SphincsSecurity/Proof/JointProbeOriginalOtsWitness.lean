import SphincsSecurity.Proof.JointProbeOriginalOtsSupport
import SphincsSecurity.Proof.JointProbeOriginalRetainedFailure

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex WinningRetainedVerifyProbeWitness)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.maskedChronologicalRetainedGameAfterFtsSecrets
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

theorem run_retained_winningOts_imp_stopped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat)
    (frame : Frame) (cache : QueryCache HashSpec)
    (hroot : RootSupport otsTable ftsTable q fuel root frame) (hvalid : frame.Valid parameter otsTable ftsTable cache)
    (pair) (hpair : pair ∈ support (run exception parameter root otsTable ftsTable
      (retainedComputation adversary parameter root q) (some frame) cache false))
    (actual : RetainedGameResult × QueryCache HashSpec)
    (hactual : actual ∈ support (OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter
      (fun index tree leaf => ftsTable (index, tree, leaf)) (OtsProbeSimulation.extendStartTable otsTable)))
    (hvalue : pair.2.1.1 = some actual.1) (hcache : pair.2.1.2 = actual.2)
    (hwitness : WinningRetainedVerifyProbeWitness parameter (OtsProbeSimulation.extendStartTable otsTable)
      (fun index tree leaf => ftsTable (index, tree, leaf)) actual) : pair.1 = none := by
  cases hframe : pair.1 with
  | none => rfl
  | some finalFrame =>
      have hf := run_valid exception parameter root otsTable ftsTable _ (some frame) cache false
        (by intro live heq; cases Option.some.inj heq; exact ⟨hvalid, rfl⟩) pair hpair finalFrame hframe
      let native : ResolvedRunResult (RetainedGameResult × OtsProbeSimulation.SplitHashCache) :=
        ⟨finalFrame.context, finalFrame.fuel,
          (actual.1, OtsProbeSimulation.replaceOrdinaryCache finalFrame.cache.1 (mergedCache parameter ftsTable finalFrame.cache.2)), otsTable⟩
      have hi : OtsProbeSimulation.ResolvedContextInvariant parameter otsTable native.context
          (OtsProbeSimulation.ordinaryQueryCache native.value.2) actual.2 := by
        simpa only [native, OtsProbeSimulation.ordinaryQueryCache_replaceOrdinaryCache, hcache] using hf.1.2.2.1
      have hr : OtsProbeSimulation.ReachableResolvedRunRel parameter otsTable (some native) actual :=
        Or.inl ⟨rfl, rfl, hi, hcache ▸ hf.1.2.2.2.1, hf.1.2.2.2.2⟩
      have hn := run_retained_native_support exception adversary parameter root otsTable ftsTable q fuel frame cache false
        hroot hvalid pair hpair finalFrame hframe actual.1 hvalue
      have hempty : OtsProbeSimulation.ensuredInitialContext ∅ =
          ({ state := LazyRevealProbe.State.empty, values := OtsProbeSimulation.emptyDeferredStructuralValues } :
            OtsProbeSimulation.DeferredContext) := by
        simp only [OtsProbeSimulation.ensuredInitialContext, Finset.image_empty]
        rfl
      rw [hempty] at hn
      exact False.elim ((OtsProbeSimulation.not_deferredCompletable_of_winningRetainedVerifyProbe adversary parameter otsTable
        (fun index tree leaf => ftsTable (index, tree, leaf)) fuel native actual.1 actual.2 hn hactual hr hwitness) hi.2.2.2.1)

theorem runRetained_winningOts_imp_stopped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) (pair) (hpair : pair ∈ support (runRetained exception adversary parameter otsTable ftsTable q fuel))
    (actual : RetainedGameResult × QueryCache HashSpec)
    (hactual : actual ∈ support (OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter
      (fun index tree leaf => ftsTable (index, tree, leaf)) (OtsProbeSimulation.extendStartTable otsTable)))
    (hvalue : pair.2.1.1 = some actual.1) (hcache : pair.2.1.2 = actual.2)
    (hwitness : WinningRetainedVerifyProbeWitness parameter (OtsProbeSimulation.extendStartTable otsTable)
      (fun index tree leaf => ftsTable (index, tree, leaf)) actual) : pair.1 = none := by
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
      exact run_retained_winningOts_imp_stopped exception adversary parameter initial.2.1 otsTable ftsTable q fuel frame initial.2.2
        hv.1 hv.2 pair hrest actual hactual hvalue hcache hwitness

def CleanOtsWitness (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option RetainedGameResult × QueryCache HashSpec) × Bool) : Prop :=
  result.2 = false ∧ ∃ value, result.1.1 = some value ∧
    WinningRetainedVerifyProbeWitness parameter (OtsProbeSimulation.extendStartTable otsTable)
      (fun index tree leaf => ftsTable (index, tree, leaf)) (value, result.1.2)

theorem runRetainedWithFailure_clean_otsWitness_imp_failure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat)
    (result) (hresult : result ∈ support (runRetainedWithFailure exception adversary parameter otsTable ftsTable q fuel))
    (hwitness : CleanOtsWitness parameter otsTable ftsTable result.1.2) : result.2 = true := by
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
  have hnone := runRetained_winningOts_imp_stopped exception adversary parameter otsTable ftsTable q fuel
    result.1 hproject actual ha hv hc hwitness
  have hcause := (runRetainedWithFailure_missing_iff exception adversary parameter otsTable ftsTable q fuel result hresult).1 hnone
  exact hcause.resolve_left (by simp [hclean])

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

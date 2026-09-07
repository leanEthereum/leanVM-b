import SphincsSecurity.Proof.JointProbeOriginalSharedSupport
import SphincsSecurity.Proof.JointProbeResolvedFtsWitness

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex ResolvedRunResult sampleOtsHashTable)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot
attribute [local irreducible] jointResolvedRetainedDetailed
attribute [local irreducible] sampleOtsHashTable

noncomputable def retainedComputation (adversary : Adversary) (parameter : PublicParameter) (root : Digest) (q : Nat) :=
  Option.map (fun rest => (root, rest)) <$>
    OtsProbeSimulation.capOuterHashQueries (retainedGameRestComputation adversary ⟨root, parameter⟩) q

theorem retainedComputation_hashBound (adversary : Adversary) (parameter : PublicParameter) (root : Digest) (q : Nat) :
    (retainedComputation adversary parameter root q).IsQueryBoundP OtsProbeSimulation.IsOuterHash q := by
  rw [retainedComputation, isQueryBoundP_map_iff]
  exact OtsProbeSimulation.capOuterHashQueries_hashBound _ q

def RootSupport (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) (root : Digest) (frame : Frame) : Prop :=
  frame.ftsFuel = q ∧
    .done false frame.state (some (⟨frame.context, frame.fuel, (root, frame.cache), otsTable⟩ : ResolvedRunResult (Digest × JointSourceCache))) ∈
      support (AdaptiveRevealProbe.runDetailed ftsTable AdaptiveRevealProbe.State.empty q
        (runJointResolved ((jointSourceNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot).run
          (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache))
          (OtsProbeSimulation.ensuredInitialContext ∅) fuel otsTable))

theorem run_retained_shared_support
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat)
    (frame : Frame) (cache : QueryCache HashSpec) (hit : Bool)
    (hroot : RootSupport otsTable ftsTable q fuel root frame) (hvalid : frame.Valid parameter otsTable ftsTable cache)
    (pair) (hpair : pair ∈ support (run exception parameter root otsTable ftsTable
      (retainedComputation adversary parameter root q) (some frame) cache hit))
    (finalFrame : Frame) (hframe : pair.1 = some finalFrame) :
    .done false finalFrame.state (some (⟨finalFrame.context, finalFrame.fuel, (pair.2.1.1, finalCache finalFrame.cache), otsTable⟩ :
      ResolvedRunResult (Option RetainedGameResult × JointSourceCache))) ∈
      support (jointResolvedRetainedDetailed adversary parameter otsTable ftsTable q fuel) := by
  have hbound : (retainedComputation adversary parameter root q).IsQueryBoundP OtsProbeSimulation.IsOuterHash frame.ftsFuel := by
    rw [hroot.1]
    exact retainedComputation_hashBound adversary parameter root q
  have htail := run_shared_support exception parameter root otsTable ftsTable _ frame cache hit hbound hvalid pair hpair finalFrame hframe
  rw [jointResolvedRetainedDetailed, jointSourceRetained, runDetailed_jointResolved_bind_probeFree]
  · rw [mem_support_bind_iff]
    refine ⟨.done false frame.state (some ⟨frame.context, frame.fuel, (root, frame.cache), otsTable⟩), hroot.2, ?_⟩
    simpa only [resumeJointResolved, ← hroot.1, retainedComputation] using htail
  · exact runJointResolved_nativeBlock_probeFree _ _ fuel otsTable _

theorem jointSourceFtsWitness_finalCache
    (parameter : PublicParameter) (ftsTable : Coordinate → Digest) (value : Option RetainedGameResult) (cache : JointSourceCache) :
    JointSourceFtsWitness parameter ftsTable (value, finalCache cache) ↔ JointSourceFtsWitness parameter ftsTable (value, cache) := by
  simp only [JointSourceFtsWitness, finalCache, prepareNativeCache, OtsProbeSimulation.replaceOrdinaryCache_replace]

theorem jointResolvedRetained_no_ftsWitness_of_sampledTable
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput)
    (ftsTable : Coordinate → Digest) (q fuel : Nat) (hots : otsTable ∈ support sampleOtsHashTable)
    (result) (hresult : result ∈ support (jointResolvedRetainedDetailed adversary parameter otsTable ftsTable q fuel)) :
    ¬ ∃ value, OtsProbeSimulation.resolvedPrefixValue (cleanJointResolved result) = some value ∧
      JointSourceFtsWitness parameter ftsTable value := by
  have hzero := (ENNReal.tsum_eq_zero.mp (probEvent_sampled_jointResolved_ftsWitness_eq_zero adversary parameter ftsTable q fuel)) otsTable
  have hmass : Pr[= otsTable | sampleOtsHashTable] ≠ 0 :=
    probOutput_ne_zero_of_mem_support (mx := sampleOtsHashTable) hots
  have hprob := (mul_eq_zero.mp hzero).resolve_left hmass
  exact (probEvent_eq_zero_iff.mp hprob) result hresult

theorem run_retained_no_ftsWitness
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat)
    (frame : Frame) (cache : QueryCache HashSpec) (hit : Bool)
    (hots : otsTable ∈ support sampleOtsHashTable)
    (hroot : RootSupport otsTable ftsTable q fuel root frame) (hvalid : frame.Valid parameter otsTable ftsTable cache)
    (pair) (hpair : pair ∈ support (run exception parameter root otsTable ftsTable
      (retainedComputation adversary parameter root q) (some frame) cache hit))
    (finalFrame : Frame) (hframe : pair.1 = some finalFrame) :
    ¬ JointSourceFtsWitness parameter ftsTable (pair.2.1.1, finalFrame.cache) := by
  have hshared := run_retained_shared_support exception adversary parameter root otsTable ftsTable q fuel frame cache hit
    hroot hvalid pair hpair finalFrame hframe
  intro hwitness
  apply jointResolvedRetained_no_ftsWitness_of_sampledTable adversary parameter otsTable ftsTable q fuel hots _ hshared
  exact ⟨(pair.2.1.1, finalCache finalFrame.cache), rfl,
    (jointSourceFtsWitness_finalCache parameter ftsTable pair.2.1.1 finalFrame.cache).2 hwitness⟩

theorem probEvent_run_retained_live_ftsWitness_eq_zero
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat)
    (frame : Frame) (cache : QueryCache HashSpec) (hit : Bool)
    (hots : otsTable ∈ support sampleOtsHashTable)
    (hroot : RootSupport otsTable ftsTable q fuel root frame) (hvalid : frame.Valid parameter otsTable ftsTable cache) :
    Pr[fun pair => ∃ finalFrame, pair.1 = some finalFrame ∧ JointSourceFtsWitness parameter ftsTable (pair.2.1.1, finalFrame.cache) |
      run exception parameter root otsTable ftsTable (retainedComputation adversary parameter root q) (some frame) cache hit] = 0 := by
  rw [probEvent_eq_zero_iff]
  rintro pair hpair ⟨finalFrame, hframe, hwitness⟩
  exact run_retained_no_ftsWitness exception adversary parameter root otsTable ftsTable q fuel frame cache hit
    hots hroot hvalid pair hpair finalFrame hframe hwitness

theorem run_retained_uncoveredFtsSecret_imp_stopped
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) (q fuel : Nat)
    (frame : Frame) (cache : QueryCache HashSpec)
    (hots : otsTable ∈ support sampleOtsHashTable)
    (hroot : RootSupport otsTable ftsTable q fuel root frame) (hvalid : frame.Valid parameter otsTable ftsTable cache)
    (pair) (hpair : pair ∈ support (run exception parameter root otsTable ftsTable
      (retainedComputation adversary parameter root q) (some frame) cache false))
    (actual : RetainedGameResult × QueryCache HashSpec)
    (hactual : actual ∈ support (OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter
      (fun index tree leaf => ftsTable (index, tree, leaf)) (OtsProbeSimulation.extendStartTable otsTable)))
    (hvalue : pair.2.1.1 = some actual.1) (hcache : pair.2.1.2 = actual.2)
    (hwitness : RetainedUncoveredFtsSecretWitness parameter
      (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)) ftsTable actual) :
    pair.1 = none := by
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
      have hn := OtsProbeSimulation.nativeUncoveredFtsWitness_of_canonical_relation adversary parameter otsTable
        (fun index tree leaf => ftsTable (index, tree, leaf)) native actual hactual rfl hi hwitness
      have hv := (OtsProbeSimulation.nativeUncoveredFtsWitness_iff_value parameter otsTable
        (fun index tree leaf => ftsTable (index, tree, leaf)) native).mp hn
      exact False.elim (run_retained_no_ftsWitness exception adversary parameter root otsTable ftsTable q fuel frame cache false
        hots hroot hvalid pair hpair finalFrame hframe ⟨actual.1, hvalue, hv⟩)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

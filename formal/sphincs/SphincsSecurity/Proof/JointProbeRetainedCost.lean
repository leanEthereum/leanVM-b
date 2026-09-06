import SphincsSecurity.Proof.JointProbeObserverCost
import SphincsSecurity.Proof.FtsProbeJointSampledBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot

theorem expectedJointNativeProbeCost_retained
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat) :
    expectedJointNativeProbeCost table ((jointSourceRetained adversary parameter q).run
      (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache)) AdaptiveRevealProbe.State.empty q
      (OtsProbeSimulation.ensuredInitialContext ∅) =
      expectedJointRetainedCharge adversary parameter table q (jointOtsQueryCharge parameter) := by
  have hroot : JointSourceImplements (jointSourceNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot)
      (liftNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot) := runJointErasedHistory_nativeBlock _
  unfold jointSourceRetained
  rw [expectedJointNativeProbeCost_source_bind table _ _ _ hroot,
    expectedJointNativeProbeCost_eq_zero_of_probeFree table _
      (jointSourceNativeBlock_probeBound _ 0 OtsProbeSimulation.maskedPublishedTreeRoot_probeFree _), zero_add,
    AdaptiveRevealProbe.runRaw_eq_detailed_of_probeFree table AdaptiveRevealProbe.State.empty q _
      (liftNativeBlock_probeFree _ _ 0 [] _ _), tsum_probOutput_map_mul]
  unfold expectedJointRetainedCharge
  apply tsum_congr
  intro result
  by_cases hresult : result ∈ support (AdaptiveRevealProbe.runDetailed table AdaptiveRevealProbe.State.empty q
      ((liftNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
        OtsProbeSimulation.emptySplitHashCache).run emptySplitHashCache))
  · congr 1
    cases result with
    | stopped hit => rfl
    | done hit state value =>
        rcases value with ⟨entry, finalCache⟩
        cases entry with
        | none => rfl
        | some entry =>
            have hraw : .done state q (some entry, finalCache) ∈ support
                (AdaptiveRevealProbe.runRaw table AdaptiveRevealProbe.State.empty q
                  ((liftNativeBlock OtsProbeSimulation.maskedPublishedTreeRoot (OtsProbeSimulation.ensuredInitialContext ∅) 0 []
                    OtsProbeSimulation.emptySplitHashCache).run emptySplitHashCache)) := by
              rw [AdaptiveRevealProbe.runRaw_eq_detailed_of_probeFree table AdaptiveRevealProbe.State.empty q _
                (liftNativeBlock_probeFree _ _ 0 [] _ _), support_map]
              exact ⟨_, hresult, rfl⟩
            have hf := hroot.raw_fields table AdaptiveRevealProbe.State.empty state q q
              (OtsProbeSimulation.ensuredInitialContext ∅) (OtsProbeSimulation.emptySplitHashCache, emptySplitHashCache)
              finalCache entry hraw
            dsimp only [AdaptiveRevealProbe.rawResultWithRemaining]
            rw [hf.1, hf.2]
            apply expectedJointNativeProbeCost_eq_observer parameter entry.value.1 table _ q _ state q le_rfl
            rw [isQueryBoundP_map_iff]
            exact OtsProbeSimulation.capOuterHashQueries_hashBound _ q
  · simp [probOutput_eq_zero_of_not_mem_support hresult]

theorem nativeFtsRetainedSource_expectedCost_eq_observer
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat) :
    OtsProbeSimulation.expectedErasedHistoryProbeCost (nativeFtsRetainedSource adversary parameter table q)
      (OtsProbeSimulation.ensuredInitialContext ∅) =
      expectedJointRetainedCharge adversary parameter table q (jointOtsQueryCharge parameter) := by
  unfold nativeFtsRetainedSource
  rw [← expectedJointNativeProbeCost_eq_finalized, expectedJointNativeProbeCost_retained]

end SphincsSecurity.Concrete.FtsProbeSimulation

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def sampledNativeFtsOtsCharge (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      OtsProbeSimulation.expectedErasedHistoryProbeCost
        (FtsProbeSimulation.nativeFtsRetainedSource adversary parameter (FtsProbeSimulation.curryFtsTableEquiv ftsSecret) q)
        (OtsProbeSimulation.ensuredInitialContext ∅)

theorem sampledNativeFtsOtsCharge_eq_jointObserver (adversary : Adversary) (q : Nat) :
    sampledNativeFtsOtsCharge adversary q = sampledJointObservedOtsCharge adversary q := by
  unfold sampledNativeFtsOtsCharge sampledJointObservedOtsCharge
  simp_rw [FtsProbeSimulation.nativeFtsRetainedSource_expectedCost_eq_observer]

theorem sampledNativeFtsOts_add_fts_charge_le_q (adversary : Adversary) (q : Nat) :
    sampledNativeFtsOtsCharge adversary q + sampledJointRetainedProbeCharge adversary q ≤ q := by
  rw [sampledNativeFtsOtsCharge_eq_jointObserver]
  exact sampledJointObservedOts_add_fts_charge_le_q adversary q

theorem sampledNativeFtsOts_add_fts_hit_le_query_rate (adversary : Adversary) (q : Nat) :
    sampledNativeFtsOtsCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ + sampledJointRetainedFtsHitRisk adversary q ≤
      (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [sampledNativeFtsOtsCharge_eq_jointObserver]
  exact sampledJointObservedOts_add_fts_hit_le_query_rate adversary q

end SphincsSecurity.Concrete

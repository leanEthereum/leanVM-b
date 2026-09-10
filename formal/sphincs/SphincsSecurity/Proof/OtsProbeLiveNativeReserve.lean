import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.CoupledQueryCost
import SphincsSecurity.Proof.MappedQueryCharge
import SphincsSecurity.Proof.OtsOpeningRefinedReserve
import SphincsSecurity.Proof.OtsProbeExecutionCharge
import SphincsSecurity.Proof.OtsProbeResolvedSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedLiveNativeOuterCharge
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (charge : (OracleWorld + SigningSpec).Domain → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ => 0)
    (fun input _ next context fuel table cache =>
      if DeferredCompletable table context then
        charge input + ∑' result, Pr[= result | runResolvedFromTable context fuel table ((impl input).run cache)] *
          match result with
          | none => 0
          | some result => next result.value.1 result.context result.remaining result.table result.value.2
      else 0) computation

theorem expectedLiveNativeOuterCharge_query_bind
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (charge : (OracleWorld + SigningSpec).Domain → ENNReal) (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    expectedLiveNativeOuterCharge impl charge (OracleSpec.query input >>= next) context fuel table cache =
      (if DeferredCompletable table context then
        charge input + ∑' result, Pr[= result | runResolvedFromTable context fuel table ((impl input).run cache)] *
          match result with
          | none => 0
          | some result => expectedLiveNativeOuterCharge impl charge (next result.value.1)
              result.context result.remaining result.table result.value.2
      else 0) := rfl

theorem expectedLiveNativeOuterCharge_eq_zero_of_not_completable
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (charge : (OracleWorld + SigningSpec).Domain → ENNReal) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hdoomed : ¬DeferredCompletable table context) :
    expectedLiveNativeOuterCharge impl charge computation context fuel table cache = 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next _ => rw [expectedLiveNativeOuterCharge_query_bind, if_neg hdoomed]

theorem expectedLiveNativeOuterCharge_le_actualOuterCharge
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (charge : (OracleWorld + SigningSpec).Domain → ENNReal)
    (actualCharge : QueryCache HashSpec → HashInput → ENNReal)
    (himpl : ∀ input, ReachableResolvedCouples parameter table (impl input)
      (unloggedMappedAdversaryImpl
        (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey) input))
    (hcharge : ∀ input actualCache, charge input ≤ outerHashQueryCharge actualCharge input actualCache)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) :
    expectedLiveNativeOuterCharge impl charge computation context fuel table cache ≤
      expectedOuterQueryCharge
        (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey)
        actualCharge computation actualCache := by
  let secretKey : SecretKey := ⟨parameter, root, fun lay tree leafIdx chainIdx =>
    truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  change _ ≤ expectedOuterQueryCharge secretKey actualCharge computation actualCache
  induction computation using OracleComp.inductionOn generalizing context fuel cache actualCache with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedLiveNativeOuterCharge_query_bind, if_pos hinvariant.2.2.2.1, expectedOuterQueryCharge_query_bind]
      apply add_le_add (hcharge input actualCache)
      have hstep := himpl input context fuel cache actualCache hinvariant hvisible hpublished
      have hcost := expected_cost_le_of_relTriple hstep
        (fun left => match left with
          | none => 0
          | some result => expectedLiveNativeOuterCharge impl charge (next result.value.1)
              result.context result.remaining result.table result.value.2)
        (fun right => expectedOuterQueryCharge secretKey actualCharge (next right.1) right.2)
        (fun _ => 0) (by
          intro left right hrelation
          simp only [add_zero]
          cases left with
          | none => exact bot_le
          | some result =>
              dsimp only
              rcases hrelation with hclean | hdoomed
              · rw [hclean.1, ← hclean.2.1]
                exact ih result.value.1 result.context result.remaining result.value.2 right.2
                  hclean.2.2.1 hclean.2.2.2.1 hclean.2.2.2.2
              · rw [expectedLiveNativeOuterCharge_eq_zero_of_not_completable impl charge
                  (next result.value.1) result.context result.remaining result.table result.value.2 (by
                    rw [hdoomed.1]
                    exact hdoomed.2.2.2)]
                exact bot_le)
      simpa only [mul_zero, tsum_zero, add_zero] using hcost

theorem reachableResolvedCouples_chronologicalNative_concrete
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : (OracleWorld + SigningSpec).Domain) :
    ReachableResolvedCouples parameter table (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input)
      (unloggedMappedAdversaryImpl
        (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey) input) := by
  cases input with
  | inl query => exact reachableResolvedCouples_probingRomImpl parameter table query
  | inr message => exact reachableResolvedCouples_maskedPublishedChronologicalSign_concrete parameter root table ftsSecret message

theorem weightedOtsOuterQueryCharge_le_refinedReserve (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (actualCache : QueryCache HashSpec) :
    otsOuterQueryCharge secretKey.parameter input * (4 / 3 : ENNReal) ≤
      outerHashQueryCharge (otsOpeningRefinedQueryReserve secretKey) input actualCache := by
  cases input with
  | inl query =>
      cases query with
      | inl n => simp [otsOuterQueryCharge, outerHashQueryCharge, hashQueryCharge]
      | inr input =>
          change otsHashInputCharge secretKey.parameter input * (4 / 3 : ENNReal) ≤ otsOpeningRefinedQueryReserve secretKey actualCache input
          unfold otsHashInputCharge
          split_ifs with hots
          · obtain ⟨position, hposition, hat⟩ := hots
            simpa only [one_mul] using otsOpeningRefinedQueryReserve_ge_four_thirds_of_atOtsPosition secretKey actualCache input position hat hposition
          · simp
  | inr message => simp [otsOuterQueryCharge, outerHashQueryCharge]

theorem expectedLiveNativeOuterCharge_mul
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (charge : (OracleWorld + SigningSpec).Domain → ENNReal) (factor : ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    expectedLiveNativeOuterCharge impl (fun input => charge input * factor) computation context fuel table cache =
      expectedLiveNativeOuterCharge impl charge computation context fuel table cache * factor := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value => simp [expectedLiveNativeOuterCharge]
  | query_bind input next ih =>
      rw [expectedLiveNativeOuterCharge_query_bind, expectedLiveNativeOuterCharge_query_bind]
      by_cases hcomplete : DeferredCompletable table context
      · simp only [if_pos hcomplete, add_mul]
        congr 1
        rw [← ENNReal.tsum_mul_right]
        apply tsum_congr
        intro result
        cases result with
        | none => simp
        | some result => simp only [ih, mul_assoc]
      · simp [hcomplete]

end SphincsSecurity.Concrete.OtsProbeSimulation

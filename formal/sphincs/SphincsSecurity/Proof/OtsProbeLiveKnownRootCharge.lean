import SphincsSecurity.Proof.OtsProbeLiveContextCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def KnownHiddenEncodingRootQuery (parameter : PublicParameter) (input : HashInput) (context : DeferredContext) : Prop :=
  ∃ (candidate : Probe) (target : Position) (output : HashOutput),
    EncodingLayerRootCandidateAt parameter input candidate ∧ candidate.coordinate = .position target ∧
      context.positionValue target = some output ∧ .position target ∉ context.state.revealed

noncomputable def knownEncodingRootOuterCharge (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (_fuel : Nat) (_cache : SplitHashCache) : ENNReal :=
  match input with
  | .inl (.inr input) => if KnownHiddenEncodingRootQuery parameter input context then 4 / 3 else 0
  | _ => 0

theorem knownEncodingRootOuterCharge_le_actualRootCharge
    (secretKey : SecretKey) (table : OtsSecretIndex → HashOutput)
    (hsecrets : secretKey.otsSecret = fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat)
    (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant secretKey.parameter table context (ordinaryQueryCache cache) actualCache)
    (hcomputed : DeferredComputationsClosed context) :
    knownEncodingRootOuterCharge secretKey.parameter input context fuel cache ≤
      outerHashQueryCharge (rootEncodingQueryCharge secretKey) input actualCache := by
  cases input with
  | inl query =>
      cases query with
      | inl n => simp [knownEncodingRootOuterCharge, outerHashQueryCharge, hashQueryCharge]
      | inr input =>
          rw [outerHashQueryCharge_hash]
          simp only [knownEncodingRootOuterCharge]
          split_ifs with hknown
          · obtain ⟨candidate, target, output, hcandidate, hposition, hvalue, _hhidden⟩ := hknown
            rw [hcomputed.rootEncodingQueryCharge_eq_four_thirds hinvariant hsecrets hcandidate hposition hvalue]
          · exact zero_le
  | inr message => simp [knownEncodingRootOuterCharge, outerHashQueryCharge]

theorem expectedLiveKnownRootCharge_le_actualRootCharge
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
      (knownEncodingRootOuterCharge parameter) computation context fuel table cache ≤
      expectedQueryCharge
        (rootEncodingQueryCharge
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey))
        (simulateQ (expandedAdversaryImpl
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey)) computation) actualCache := by
  let secretKey : SecretKey := ⟨parameter, root,
    fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩
  have hbound : expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
      (knownEncodingRootOuterCharge parameter) computation context fuel table cache ≤
      expectedOuterQueryCharge secretKey (rootEncodingQueryCharge secretKey) computation actualCache :=
    expectedLiveNativeContextCharge_le_actualOuterCharge parameter root table ftsSecret
      (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) (knownEncodingRootOuterCharge parameter)
      (rootEncodingQueryCharge secretKey)
      (reachableResolvedCouples_chronologicalNative_concrete parameter root table ftsSecret)
      (knownEncodingRootOuterCharge_le_actualRootCharge secretKey table rfl)
      computation context fuel cache actualCache hinvariant hvisible hpublished hcomputed
  exact hbound.trans (expectedOuterQueryCharge_le_expanded secretKey (rootEncodingQueryCharge secretKey) computation actualCache)

def KnownHiddenEncodingRootSelection (parameter : PublicParameter) : Option CanonicalQuerySelection → Prop
  | none => False
  | some selection => match selection.input with
      | .inl (.inr input) => KnownHiddenEncodingRootQuery parameter input selection.context
      | _ => False

theorem knownEncodingRootSelection_charge_eq_indicator
    (parameter : PublicParameter) (selection : Option CanonicalQuerySelection) :
    CanonicalQuerySelection.charge (knownEncodingRootOuterCharge parameter) selection =
      if KnownHiddenEncodingRootSelection parameter selection then (4 / 3 : ENNReal) else 0 := by
  cases selection with
  | none => simp [CanonicalQuerySelection.charge, KnownHiddenEncodingRootSelection]
  | some selection =>
      rcases selection with ⟨input, context, fuel, table, cache⟩
      cases input with
      | inl query => cases query <;> simp [CanonicalQuerySelection.charge, knownEncodingRootOuterCharge, KnownHiddenEncodingRootSelection]
      | inr message => simp [CanonicalQuerySelection.charge, knownEncodingRootOuterCharge, KnownHiddenEncodingRootSelection]

theorem expected_knownEncodingRootSelection_charge_eq_probability
    (parameter : PublicParameter) (run : ProbComp (Option CanonicalQuerySelection)) :
    (∑' selection, Pr[= selection | run] * CanonicalQuerySelection.charge (knownEncodingRootOuterCharge parameter) selection) =
      Pr[KnownHiddenEncodingRootSelection parameter | run] * (4 / 3 : ENNReal) := by
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro selection
  rw [knownEncodingRootSelection_charge_eq_indicator]
  split_ifs <;> simp

theorem tsum_knownEncodingRootSelection_probability_eq_charge
    (parameter : PublicParameter)
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    (∑' ordinal, Pr[KnownHiddenEncodingRootSelection parameter |
      liveNativeQuerySelection impl computation ordinal context fuel table cache]) * (4 / 3 : ENNReal) =
      expectedLiveNativeContextCharge impl (knownEncodingRootOuterCharge parameter) computation context fuel table cache := by
  rw [← tsum_liveNativeQuerySelection_charge, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro ordinal
  exact (expected_knownEncodingRootSelection_charge_eq_probability parameter _).symm

theorem sum_knownEncodingRootSelection_probability_le_charge
    (parameter : PublicParameter)
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    (∑ ordinal ∈ Finset.range q, Pr[KnownHiddenEncodingRootSelection parameter |
      liveNativeQuerySelection impl computation ordinal context fuel table cache]) * (4 / 3 : ENNReal) ≤
      expectedLiveNativeContextCharge impl (knownEncodingRootOuterCharge parameter) computation context fuel table cache := by
  rw [← tsum_knownEncodingRootSelection_probability_eq_charge]
  exact mul_le_mul' (ENNReal.sum_le_tsum (Finset.range q)) le_rfl

end SphincsSecurity.Concrete.OtsProbeSimulation

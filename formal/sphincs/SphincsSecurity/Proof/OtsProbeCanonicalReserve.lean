import SphincsSecurity.Proof.OtsProbeCanonicalCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

noncomputable def canonicalOtsHashCharge
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext) : ℝ≥0∞ := by
  classical
  exact if ∃ position : Position, IsOtsPosition position ∧ AtPosition parameter input position then 4 / 3
    else (materializedCandidateCharge (materializedDeferredState context)
      (decodeEncodingLayerRootCandidate? parameter input) : ℝ≥0∞) * (4 / 3)

noncomputable def canonicalOtsOuterCharge (parameter : PublicParameter) :
    (OracleWorld + SigningSpec).Domain → DeferredContext → Nat → SplitHashCache → ℝ≥0∞
  | .inl (.inr input), context, _, _ => canonicalOtsHashCharge parameter input context
  | _, _, _, _ => 0

set_option maxRecDepth 100000 in
theorem canonicalOtsHashCharge_le_refinedReserve
    {secretKey : SecretKey} {table : OtsSecretIndex → HashOutput}
    {context : DeferredContext} {ordinaryCache actualCache : QueryCache HashSpec}
    (hinvariant : ResolvedContextInvariant secretKey.parameter table context ordinaryCache actualCache)
    (hcomputed : DeferredComputationsClosed context)
    (hsecrets : secretKey.otsSecret = fun lay tree leafIdx chainIdx =>
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩))
    (input : HashInput) :
    canonicalOtsHashCharge secretKey.parameter input context ≤
      otsOpeningRefinedQueryReserve secretKey actualCache input := by
  classical
  unfold canonicalOtsHashCharge
  split_ifs with hots
  · obtain ⟨position, hposition, hat⟩ := hots
    exact otsOpeningRefinedQueryReserve_ge_four_thirds_of_atOtsPosition secretKey actualCache input
      position hat hposition
  · cases hdecode : decodeEncodingLayerRootCandidate? secretKey.parameter input with
    | none => simp [materializedCandidateCharge]
    | some candidate =>
        have hcandidate := (decodeEncodingLayerRootCandidate?_eq_some_iff secretKey.parameter input candidate).mp hdecode
        obtain ⟨position, hcoordinate, _hroot⟩ := encodingLayerRootCandidateAt_isLayerRoot hcandidate
        simp only [materializedCandidateCharge]
        split_ifs with hblocked hknown
        · simp
        · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hknown
          have hvalue : context.positionValue position = some output := by
            simpa only [hcoordinate, materializedDeferredState] using houtput
          simpa only [Nat.cast_one, one_mul] using
            hcomputed.refinedReserve_of_encoding_candidate hinvariant hsecrets hcandidate hcoordinate hvalue
        · simp

set_option maxRecDepth 100000 in
theorem expectedCanonicalOtsCharge_le_actualReserve
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) (actualCache : QueryCache HashSpec)
    (hinvariant : ResolvedContextInvariant parameter table context (ordinaryQueryCache cache) actualCache)
    (hvisible : VisibleResolvedComputationsCached parameter table context actualCache)
    (hpublished : PublishedValues context.state) (hcomputed : DeferredComputationsClosed context) :
    expectedCanonicalQueryCharge parameter root ftsSecret (canonicalOtsOuterCharge parameter)
        computation context fuel table cache ≤
      expectedQueryCharge
        (otsOpeningRefinedQueryReserve
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey))
        (simulateQ (expandedAdversaryImpl
          (⟨parameter, root, fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩),
            ftsSecret⟩ : SecretKey)) computation) actualCache := by
  apply le_trans ?_ (expectedOuterQueryCharge_le_expanded _ _ computation actualCache)
  apply expectedCanonicalQueryCharge_le_outerQueryCharge parameter root table ftsSecret
    (canonicalOtsOuterCharge parameter) _ ?_ computation context fuel cache actualCache
    hinvariant hvisible hpublished hcomputed
  intro input nextContext remaining nextCache concreteCache hcontext _hvisible _hpublished hcomputed
  cases input with
  | inl query =>
      cases query with
      | inl n => exact le_rfl
      | inr input =>
          change canonicalOtsHashCharge parameter input nextContext ≤
            otsOpeningRefinedQueryReserve
              (⟨parameter, root, fun lay tree leafIdx chainIdx =>
                truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩ : SecretKey) concreteCache input
          exact canonicalOtsHashCharge_le_refinedReserve
            (secretKey := ⟨parameter, root, fun lay tree leafIdx chainIdx =>
              truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩), ftsSecret⟩) hcontext hcomputed rfl input
  | inr message => exact le_rfl

end SphincsSecurity.Concrete.OtsProbeSimulation

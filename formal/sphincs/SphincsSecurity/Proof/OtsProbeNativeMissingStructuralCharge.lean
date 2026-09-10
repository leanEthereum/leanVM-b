import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeLiveContextCharge
import SphincsSecurity.Proof.OtsProbePrivateMissingHash

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def nativeMissingStructuralCharge
    (target : Position) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (_fuel : Nat) (_cache : SplitHashCache) : ENNReal :=
  match input with
  | .inl (.inr input) => privateMissingCandidateAllowance target table context
      (purePlanProbingHashQuery parameter input context.state).candidate?
  | _ => 0

theorem privateMissingAllowance_chronologicalQuery
    (target : Position) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    privateLiveMissingProbeAllowance target ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)
        context fuel table =
      if DeferredCompletable table context then nativeMissingStructuralCharge target parameter table input context fuel cache else 0 := by
  cases input with
  | inl input =>
      cases input with
      | inl n =>
          simpa [nativeMissingStructuralCharge, maskedChronologicalExpandedAdversaryImpl, probingRomImpl, maskedChronologicalSigningImpl] using
            (privateLiveMissingProbeAllowance_eq_zero_of_probeFree target _ context fuel table (splitUniformImpl_probeFree n cache))
      | inr hashInput => exact privateMissingAllowance_probingHashQuery target parameter hashInput cache context fuel table hconsistent hstarts
  | inr message =>
      simpa [nativeMissingStructuralCharge, maskedChronologicalExpandedAdversaryImpl, probingRomImpl, maskedChronologicalSigningImpl] using
        (privateLiveMissingProbeAllowance_eq_zero_of_probeFree target _ context fuel table
          (maskedPublishedChronologicalSign_probeFree parameter root ftsSecret message cache))

theorem privateMissingAllowance_chronological_eq_nativeCharge
    (target : Position) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    privateLiveMissingProbeAllowance target
      ((simulateQ (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret) computation).run cache) context fuel table =
      expectedLiveNativeContextCharge (maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret)
        (nativeMissingStructuralCharge target parameter table) computation context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing context fuel table cache with
  | pure value => simp [privateLiveMissingProbeAllowance, expectedLiveNativeContextCharge]
  | query_bind input next ih =>
      by_cases hcomplete : DeferredCompletable table context
      · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          privateLiveMissingProbeAllowance_bind target _ _ context fuel table hconsistent hstarts,
          privateMissingAllowance_chronologicalQuery target parameter root ftsSecret input context fuel table cache hconsistent hstarts,
          if_pos hcomplete, expectedLiveNativeContextCharge_query_bind, if_pos hcomplete]
        congr 1
        apply tsum_congr
        intro option
        by_cases hoption : option ∈ support (runResolvedFromTable context fuel table
            ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache))
        · cases option with
          | none => simp [privateMissingContinuationAllowance]
          | some result =>
              have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hoption
              dsimp only [privateMissingContinuationAllowance]
              rw [hcore.1, ih result.value.1 result.context result.remaining table result.value.2 hcore.2.1 hcore.2.2]
        · simp [probOutput_eq_zero_of_not_mem_support hoption]
      · rw [privateLiveMissingProbeAllowance_eq_zero_of_not_completable target _ context fuel table hcomplete,
          expectedLiveNativeContextCharge_eq_zero_of_not_completable _ _ _ context fuel table cache hcomplete]

end SphincsSecurity.Concrete.OtsProbeSimulation

import SphincsSecurity.Proof.OtsProbeNativeJointSecrets
import SphincsSecurity.Proof.FirstParentOtsGame

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

def FirstParentOrSecretWitness (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord) : Prop :=
  FirstParentOrOtsWitness parameter otsSecret ftsSecret result ∨
    FtsProbeSimulation.RetainedUncoveredFtsSecretWitness parameter otsSecret
      (fun coordinate => ftsSecret coordinate.1 coordinate.2.1 coordinate.2.2) result.1

theorem probEvent_firstParentOrSecretWitness_le_native_joint
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
    Pr[FirstParentOrSecretWitness parameter otsSecret ftsSecret |
      runFirstException (CleanParentSettlement parameter otsSecret ftsSecret)
        (retainedAfterSecretsComputation adversary parameter otsSecret ftsSecret) ∅ none] ≤
      Pr[fun trace => trace.1 = none ∨ NativeFtsTraceEvent parameter table ftsSecret trace |
        nativeRetainedParentTrace adversary parameter table ftsSecret fuel] := by
  dsimp only
  have hbound := probEvent_parentOtsOrFtsWitness_le_native_joint adversary parameter table ftsSecret fuel
  apply le_trans _ hbound
  apply probEvent_le_of_relTriple (relTriple_firstParentRetained_prehit adversary parameter table ftsSecret)
  intro left right hrel hevent
  rcases hevent with (hparent | hwitness) | hfts
  · exact Or.inl (Or.inl (hrel.2 hparent))
  · apply Or.inl
    apply Or.inr
    rw [WinningRetainedVerifyProbeAfterOtsSecret, hrel.1] at hwitness
    exact (winningRetainedVerifyProbe_congr_tableOtsSecret parameter ftsSecret _ _
      (by rw [tableOtsSecret_tableOfOtsSecret, tableOtsSecret_extendStartTable]; rfl) _).mp hwitness
  · apply Or.inr
    rw [hrel.1] at hfts
    have hsecrets : tableOtsSecret (extendStartTable table) =
        fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
      funext lay tree leafIdx chainIdx
      rfl
    simpa only [hsecrets] using hfts

theorem probEvent_firstParentOrSecretWitness_le_native_failure_add_fts
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    let otsSecret := fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)
    Pr[FirstParentOrSecretWitness parameter otsSecret ftsSecret |
      runFirstException (CleanParentSettlement parameter otsSecret ftsSecret)
        (retainedAfterSecretsComputation adversary parameter otsSecret ftsSecret) ∅ none] ≤
      Pr[fun verdict => verdict = true | nativeTerminalFailureAfterRoot Finset.univ adversary parameter table ftsSecret fuel] +
        Pr[NativeFtsTraceEvent parameter table ftsSecret | nativeRetainedParentTrace adversary parameter table ftsSecret fuel] := by
  apply (probEvent_firstParentOrSecretWitness_le_native_joint adversary parameter table ftsSecret fuel).trans
  have hnone := probEvent_nativeRetainedParentTrace_none_le_terminalFailure adversary parameter table ftsSecret fuel
  have heq := (evalDist_nativeTerminalFailureAfterRoot_eq_chronological ∅ adversary parameter table ftsSecret fuel).trans
    (evalDist_nativeTerminalFailureAfterRoot_eq_chronological Finset.univ adversary parameter table ftsSecret fuel).symm
  rw [_root_.OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) heq] at hnone
  exact (probEvent_or_le _ _ _).trans (add_le_add hnone le_rfl)

def SampledFirstParentOrSecretWitness
    (result : SampledSecrets × ((RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord)) : Prop :=
  FirstParentOrSecretWitness result.1.parameter result.1.otsSecret result.1.ftsSecret result.2

noncomputable def sampledNativeFtsWitnessRisk (adversary : Adversary) (fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | sampleOtsHashTable] *
        Pr[NativeFtsTraceEvent parameter table ftsSecret | nativeRetainedParentTrace adversary parameter table ftsSecret fuel]

theorem probEvent_sampledFirstParentOrSecretWitness_le_native_failure_add_fts
    (adversary : Adversary) (fuel : Nat) :
    Pr[SampledFirstParentOrSecretWitness | sampledFirstParentRetainedGame adversary] ≤
      Pr[fun verdict => verdict = true | sampledNativeTerminalFailure adversary fuel] +
        sampledNativeFtsWitnessRisk adversary fuel := by
  unfold sampledFirstParentRetainedGame sampledNativeTerminalFailure sampledNativeFtsWitnessRisk
  simp only [sampleSecrets, bind_assoc, bind_pure_comp, bind_map_left, probEvent_bind_eq_tsum, probEvent_map,
    Function.comp_def, SampledFirstParentOrSecretWitness]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro parameter
  rw [← mul_add]
  have hcoupled := expected_cost_le_of_relTriple (relTriple_symm relTriple_uniformOtsHashTable_sampleOtsSecrets)
    (fun otsSecret => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      Pr[FirstParentOrSecretWitness parameter otsSecret ftsSecret |
        runFirstException (CleanParentSettlement parameter otsSecret ftsSecret)
          (retainedAfterSecretsComputation adversary parameter otsSecret ftsSecret) ∅ none])
    (fun table => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      (Pr[fun verdict => verdict = true | nativeTerminalFailureAfterRoot Finset.univ adversary parameter table ftsSecret fuel] +
        Pr[NativeFtsTraceEvent parameter table ftsSecret | nativeRetainedParentTrace adversary parameter table ftsSecret fuel]))
    (fun _ => 0) (by
      intro otsSecret table hsecrets
      simp only [add_zero]
      rw [← hsecrets]
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      exact mul_le_mul' le_rfl (probEvent_firstParentOrSecretWitness_le_native_failure_add_fts adversary parameter table ftsSecret fuel))
  apply mul_le_mul' le_rfl
  calc
    _ ≤ ∑' table, Pr[= table | sampleOtsHashTable] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          (Pr[fun verdict => verdict = true | nativeTerminalFailureAfterRoot Finset.univ adversary parameter table ftsSecret fuel] +
            Pr[NativeFtsTraceEvent parameter table ftsSecret | nativeRetainedParentTrace adversary parameter table ftsSecret fuel]) := by
      simpa only [sampleOtsHashTable, mul_zero, tsum_zero, add_zero] using hcoupled
    _ = _ := by
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm, ← ENNReal.tsum_add]
      apply tsum_congr
      intro ftsSecret
      rw [← ENNReal.tsum_add]
      apply tsum_congr
      intro table
      ring

noncomputable def sampledNativeJointSecretRisk (adversary : Adversary) (fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | sampleOtsHashTable] *
        Pr[fun trace => trace.1 = none ∨ NativeFtsTraceEvent parameter table ftsSecret trace |
          nativeRetainedParentTrace adversary parameter table ftsSecret fuel]

theorem probEvent_sampledFirstParentOrSecretWitness_le_native_joint
    (adversary : Adversary) (fuel : Nat) :
    Pr[SampledFirstParentOrSecretWitness | sampledFirstParentRetainedGame adversary] ≤
      sampledNativeJointSecretRisk adversary fuel := by
  unfold sampledFirstParentRetainedGame sampledNativeJointSecretRisk
  simp only [sampleSecrets, bind_assoc, bind_pure_comp, bind_map_left, probEvent_bind_eq_tsum, probEvent_map,
    Function.comp_def, SampledFirstParentOrSecretWitness]
  apply ENNReal.tsum_le_tsum
  intro parameter
  have hcoupled := expected_cost_le_of_relTriple (relTriple_symm relTriple_uniformOtsHashTable_sampleOtsSecrets)
    (fun otsSecret => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      Pr[FirstParentOrSecretWitness parameter otsSecret ftsSecret |
        runFirstException (CleanParentSettlement parameter otsSecret ftsSecret)
          (retainedAfterSecretsComputation adversary parameter otsSecret ftsSecret) ∅ none])
    (fun table => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      Pr[fun trace => trace.1 = none ∨ NativeFtsTraceEvent parameter table ftsSecret trace |
        nativeRetainedParentTrace adversary parameter table ftsSecret fuel])
    (fun _ => 0) (by
      intro otsSecret table hsecrets
      simp only [add_zero]
      rw [← hsecrets]
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      exact mul_le_mul' le_rfl (probEvent_firstParentOrSecretWitness_le_native_joint adversary parameter table ftsSecret fuel))
  apply mul_le_mul' le_rfl
  calc
    _ ≤ ∑' table, Pr[= table | sampleOtsHashTable] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          Pr[fun trace => trace.1 = none ∨ NativeFtsTraceEvent parameter table ftsSecret trace |
            nativeRetainedParentTrace adversary parameter table ftsSecret fuel] := by
      simpa only [sampleOtsHashTable, mul_zero, tsum_zero, add_zero] using hcoupled
    _ = _ := by
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro ftsSecret
      apply tsum_congr
      intro table
      exact mul_left_comm _ _ _

end SphincsSecurity.Concrete.OtsProbeSimulation

import SphincsSecurity.Proof.OtsProbeNativeFtsWitness
import SphincsSecurity.Proof.FirstParentOtsWitness

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot instFintypePosition
set_option backward.isDefEq.respectTransparency false

def ParentOtsOrFtsWitness (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (RetainedGameResult × (ViewedFullTraceState × Bool)) × List PrehitQuerySnapshot) : Prop :=
  ParentOrRetainedOtsWitness parameter table ftsSecret result ∨
    FtsProbeSimulation.RetainedUncoveredFtsSecretWitness parameter (tableOtsSecret (extendStartTable table))
      (fun coordinate => ftsSecret coordinate.1 coordinate.2.1 coordinate.2.2)
      (result.1.1, result.1.2.1.cache)

def NativeFtsTraceEvent (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (trace : Option (ResolvedRunResult (RetainedGameResult × SplitHashCache)) × List CanonicalQuerySelection) : Prop :=
  ∃ result, trace.1 = some result ∧ NativeUncoveredFtsWitness parameter table ftsSecret result

set_option maxHeartbeats 800000 in
theorem probEvent_parentOtsOrFtsWitness_le_native_joint
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[ParentOtsOrFtsWitness parameter table ftsSecret | prehitRetainedQueryTrace adversary parameter table ftsSecret] ≤
      Pr[fun trace => trace.1 = none ∨ NativeFtsTraceEvent parameter table ftsSecret trace |
        nativeRetainedParentTrace adversary parameter table ftsSecret fuel] := by
  have hcoupled := relTriple_nativeRetainedParentTrace_prehit adversary parameter table ftsSecret fuel
  have hs := FtsProbeSimulation.relTriple_and_right_support
    (FtsProbeSimulation.relTriple_and_left_support hcoupled
      (fun result => result ∈ support (nativeRetainedParentTrace adversary parameter table ftsSecret fuel))
      (by intro _ hresult; exact hresult))
  apply probEvent_le_of_relTriple (relTriple_symm hs)
  rintro actual ⟨native, history⟩ hrel hevent
  cases native with
  | none => exact Or.inl rfl
  | some result =>
      have hcanonical := hrel.1.1.1.1.1
      have hactual : (actual.1.1, actual.1.2.1.cache) ∈ support
          (actualRetainedGameAfterTable adversary parameter ftsSecret (extendStartTable table)) := by
        rw [← prehitRetainedQueryTrace_cache_projection, support_map]
        exact ⟨actual, hrel.2, rfl⟩
      rcases hevent with (hearly | hwitness) | hfts
      · exact Or.inl (hrel.1.1.2 hearly)
      · have hreachable : ReachableResolvedRunRel parameter table (some result) (actual.1.1, actual.1.2.1.cache) :=
          Or.inl ⟨hcanonical.1, hcanonical.2.1, hcanonical.2.2.1, hcanonical.2.2.2.1, hcanonical.2.2.2.2.1⟩
        exact False.elim ((not_deferredCompletable_of_winningRetainedVerifyProbe adversary parameter table ftsSecret
          fuel result actual.1.1 actual.1.2.1.cache
          (mem_support_raw_of_nativeRetainedParentTrace adversary parameter table ftsSecret fuel result history hrel.1.2)
          hactual hreachable hwitness) hcanonical.2.2.1.2.2.2.1)
      · exact Or.inr ⟨result, rfl, nativeUncoveredFtsWitness_of_canonical_relation adversary parameter table ftsSecret
          result (actual.1.1, actual.1.2.1.cache) hactual hcanonical.2.1 hcanonical.2.2.1 hfts⟩

theorem probEvent_nativeRetainedParentTrace_none_le_terminalFailure
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun trace => trace.1 = none | nativeRetainedParentTrace adversary parameter table ftsSecret fuel] ≤
      Pr[fun verdict => verdict = true | nativeTerminalFailureAfterRoot ∅ adversary parameter table ftsSecret fuel] := by
  rw [← nativeRetainedParentTrace_finish, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro trace
  by_cases hnone : trace.1 = none
  · rw [if_pos hnone, hnone]
    simp [finishResolvedRunIsNone, finishResolvedRun]
  · simp [hnone]

theorem probEvent_parentOtsOrFtsWitness_le_native_failure_add_fts
    (adversary : Adversary) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[ParentOtsOrFtsWitness parameter table ftsSecret | prehitRetainedQueryTrace adversary parameter table ftsSecret] ≤
      Pr[fun verdict => verdict = true | nativeTerminalFailureAfterRoot ∅ adversary parameter table ftsSecret fuel] +
        Pr[NativeFtsTraceEvent parameter table ftsSecret | nativeRetainedParentTrace adversary parameter table ftsSecret fuel] :=
  (probEvent_parentOtsOrFtsWitness_le_native_joint adversary parameter table ftsSecret fuel).trans
    ((probEvent_or_le _ _ _).trans (add_le_add
      (probEvent_nativeRetainedParentTrace_none_le_terminalFailure adversary parameter table ftsSecret fuel) le_rfl))

end SphincsSecurity.Concrete.OtsProbeSimulation

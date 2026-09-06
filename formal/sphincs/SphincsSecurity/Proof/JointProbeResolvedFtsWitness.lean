import SphincsSecurity.Proof.JointProbeResolvedJointEvent

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex sampleOtsHashTable)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] jointRetainedDetailed OtsProbeSimulation.maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

def JointSourceFtsWitness (parameter : PublicParameter) (table : Coordinate → Digest)
    (value : Option RetainedGameResult × JointSourceCache) : Prop :=
  ∃ retained, value.1 = some retained ∧
    OtsProbeSimulation.UncoveredFtsValueWitness parameter (fun index tree leaf => table (index, tree, leaf))
      (retained, OtsProbeSimulation.replaceOrdinaryCache value.2.1 (mergedCache parameter table value.2.2))

theorem jointRetainedCleanHistory_no_ftsWitness
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat)
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (NativeStepResult (Option RetainedGameResult) × SplitHashCache))
    (hresult : result ∈ support (jointRetainedDetailed adversary parameter table q)) :
    ¬∃ value, OtsProbeSimulation.historyPrefixValue (jointRetainedCleanHistory result) = some value ∧
      JointSourceFtsWitness parameter table value := by
  intro hwitness
  cases result with
  | stopped hit => simp [jointRetainedCleanHistory, cleanJointHistory, AdaptiveRevealProbe.DetailedResult.mapValue,
      OtsProbeSimulation.historyPrefixValue] at hwitness
  | done hit state result =>
      cases hit with
      | true => simp [jointRetainedCleanHistory, cleanJointHistory, AdaptiveRevealProbe.DetailedResult.mapValue,
          OtsProbeSimulation.historyPrefixValue] at hwitness
      | false =>
          rcases result with ⟨entry, cache⟩
          cases entry with
          | none => simp [jointRetainedCleanHistory, cleanJointHistory, AdaptiveRevealProbe.DetailedResult.mapValue,
              packJointStepResult, OtsProbeSimulation.historyPrefixValue] at hwitness
          | some entry =>
              rcases hwitness with ⟨value, hvalue, retained, hretained, hwitness⟩
              simp only [jointRetainedCleanHistory, cleanJointHistory, AdaptiveRevealProbe.DetailedResult.mapValue,
                packJointStepResult, Option.map_some, OtsProbeSimulation.historyPrefixValue, Option.some.injEq] at hvalue
              subst value
              rcases retained with ⟨root, ⟨⟨forgery, log⟩, verified⟩⟩
              exact jointRetainedDetailed_no_uncovered_value adversary parameter table q state cache entry
                root forgery log verified hretained hresult hwitness

theorem probEvent_nativeFtsErased_ftsWitness_eq_zero
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat) :
    Pr[fun result => ∃ value, OtsProbeSimulation.historyPrefixValue result = some (some value) ∧
      JointSourceFtsWitness parameter table value | nativeFtsRetainedErasedHistory adversary parameter table q] = 0 := by
  have hzero : Pr[fun result => ∃ value, OtsProbeSimulation.historyPrefixValue result = some value ∧
      JointSourceFtsWitness parameter table value |
      jointRetainedCleanHistory <$> jointRetainedDetailed adversary parameter table q] = 0 := by
    rw [probEvent_map, probEvent_eq_zero_iff]
    exact jointRetainedCleanHistory_no_ftsWitness adversary parameter table q
  rw [jointRetainedCleanHistory_eq_nativeFts, probEvent_map] at hzero
  apply Eq.trans _ hzero
  apply probEvent_congr' _ rfl
  intro result _
  cases result with
  | none => simp [OtsProbeSimulation.historyPrefixValue, flattenOptionalHistory]
  | some entry =>
      cases hvalue : entry.value <;>
        simp [OtsProbeSimulation.historyPrefixValue, flattenOptionalHistory, hvalue]

theorem probEvent_sampled_nativeFtsResolved_ftsWitness_eq_zero
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q fuel : Nat) :
    (∑' otsTable, Pr[= otsTable | sampleOtsHashTable] *
      Pr[fun result => ∃ value, OtsProbeSimulation.resolvedPrefixValue result = some (some value) ∧
        JointSourceFtsWitness parameter table value |
        nativeFtsRetainedResolved adversary parameter otsTable table q fuel]) = 0 := by
  apply le_antisymm _ bot_le
  have h := OtsProbeSimulation.probEvent_sampled_resolved_value_le_erased_history ∅
    (nativeFtsRetainedSource adversary parameter table q) fuel
    (fun result => ∃ value, result = some (some value) ∧ JointSourceFtsWitness parameter table value) (by simp)
  exact h.trans_eq (probEvent_nativeFtsErased_ftsWitness_eq_zero adversary parameter table q)

theorem probEvent_sampled_jointResolved_ftsWitness_eq_zero
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q fuel : Nat) :
    (∑' otsTable, Pr[= otsTable | sampleOtsHashTable] *
      Pr[fun result => ∃ value, OtsProbeSimulation.resolvedPrefixValue (cleanJointResolved result) = some value ∧
        JointSourceFtsWitness parameter table value |
        jointResolvedRetainedDetailed adversary parameter otsTable table q fuel]) = 0 := by
  apply Eq.trans _ (probEvent_sampled_nativeFtsResolved_ftsWitness_eq_zero adversary parameter table q fuel)
  apply tsum_congr
  intro otsTable
  apply congrArg (fun risk => Pr[= otsTable | sampleOtsHashTable] * risk)
  have hp := congrArg (fun computation => Pr[fun result =>
    ∃ value, OtsProbeSimulation.resolvedPrefixValue result = some value ∧ JointSourceFtsWitness parameter table value | computation])
    (jointResolvedRetained_clean_eq_native adversary parameter otsTable table q fuel)
  simp only [probEvent_map, Function.comp_def] at hp
  apply hp.trans
  apply probEvent_congr' _ rfl
  intro result _
  cases result with
  | none => simp [OtsProbeSimulation.resolvedPrefixValue, flattenOptionalResolved]
  | some entry =>
      cases hvalue : entry.value <;> simp [OtsProbeSimulation.resolvedPrefixValue, flattenOptionalResolved, hvalue]

end SphincsSecurity.Concrete.FtsProbeSimulation

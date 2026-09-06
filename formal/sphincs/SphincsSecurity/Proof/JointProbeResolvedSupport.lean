import SphincsSecurity.Proof.JointProbeResolvedSigner

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem mem_support_jointResolved_bind_done_some
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (left : JointSource α) (next : α → JointSource β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (result : ResolvedRunResult (β × JointSourceCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hfree : (runJointResolved (left.run cache) context fuel otsTable).IsQueryBoundP AdaptiveRevealProbe.IsProbe 0)
    (hresult : .done false finalState (some result) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved ((left >>= next).run cache) context fuel otsTable))) :
    ∃ stepState entry,
      .done false stepState (some entry) ∈ support
        (AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointResolved (left.run cache) context fuel otsTable)) ∧
      .done false finalState (some result) ∈ support
        (AdaptiveRevealProbe.runDetailed table stepState ftsFuel
          (runJointResolved ((next entry.value.1).run entry.value.2) entry.context entry.remaining entry.table)) := by
  rw [StateT.run_bind, runJointResolved_bind, AdaptiveRevealProbe.runDetailed_bind_probeFree table state ftsFuel _ _ hfree,
    mem_support_bind_iff] at hresult
  obtain ⟨detailed, hleft, hnext⟩ := hresult
  obtain ⟨stepState, value, heq, hstepClean⟩ :=
    AdaptiveRevealProbe.runDetailed_probeFree_support table state ftsFuel _ hfree hclean detailed hleft
  subst detailed
  cases value with
  | none => simp [AdaptiveRevealProbe.runDetailed, hstepClean] at hnext
  | some entry => exact ⟨stepState, entry, hleft, hnext⟩

theorem revealedSynced_jointSourcePublication
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option OtsProbeSimulation.ChronologicalLayerPart)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (result : ResolvedRunResult (Option Signature × JointSourceCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache.2) (hcached : HiddenIndexCached index cache.2)
    (hresult : .done false finalState (some result) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        (runJointResolved ((jointSourcePublication parameter randomness index leaves ftsPath layers).run cache) context fuel otsTable))) :
    RevealedSynced parameter table finalState result.value.2.2 := by
  dsimp only [jointSourcePublication, StateT.run] at hresult
  rw [runJointResolved_bind, runJointResolved_native, AdaptiveRevealProbe.runDetailed_liftProbComp_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨entry, _, hresult⟩ := hresult
  cases entry with
  | none => simp [AdaptiveRevealProbe.runDetailed, hclean] at hresult
  | some entry =>
      cases hbody : entry.value.1 with
      | none =>
          simp only [hbody, runJointResolved_pure, AdaptiveRevealProbe.runDetailed, construct_pure, hclean,
            mem_support_pure_iff, AdaptiveRevealProbe.DetailedResult.done.injEq, Option.some.injEq] at hresult
          obtain ⟨_, hstate, hvalue⟩ := hresult
          subst finalState
          subst result
          exact hsynced
      | some body =>
          simp only [hbody] at hresult
          rw [runJointResolved_map, runJointResolved_fts, Functor.map_map,
            AdaptiveRevealProbe.runDetailed_mapValue, support_map] at hresult
          obtain ⟨detailed, hdetailed, heq⟩ := hresult
          cases detailed with
          | stopped hit => simp [AdaptiveRevealProbe.DetailedResult.mapValue] at heq
          | done hit selectedState selected =>
              simp only [AdaptiveRevealProbe.DetailedResult.mapValue, Option.map_some,
                AdaptiveRevealProbe.DetailedResult.done.injEq, Option.some.injEq] at heq
              obtain ⟨hhit, hstate, hvalue⟩ := heq
              subst hit
              subst finalState
              subst result
              exact revealedSynced_of_mem_runDetailed_revealSelectedFtsSecrets parameter table index leaves
                state selectedState ftsFuel cache.2 selected.2 hclean hsynced hcached selected.1 hdetailed

end SphincsSecurity.Concrete.FtsProbeSimulation

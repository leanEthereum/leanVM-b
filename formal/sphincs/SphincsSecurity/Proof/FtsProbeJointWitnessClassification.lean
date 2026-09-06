import SphincsSecurity.Proof.FtsProbeRetainedVerifierEvidence

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] OtsProbeSimulation.maskedPublishedTreeRoot

theorem jointRetainedDetailed_no_uncovered_value
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat)
    (finalState : AdaptiveRevealProbe.State Coordinate) (finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (Option RetainedGameResult × OtsProbeSimulation.SplitHashCache))
    (root : Digest) (forgery : Forgery) (log : QueryLog SigningSpec) (verified : Bool)
    (hvalue : entry.value.1 = some (root, ((forgery, log), verified)))
    (hresult : .done false finalState (some entry, finalCache) ∈ support (jointRetainedDetailed adversary parameter table q)) :
    ¬OtsProbeSimulation.UncoveredFtsValueWitness parameter (fun index tree leaf => table (index, tree, leaf))
      ((root, ((forgery, log), verified)),
        OtsProbeSimulation.replaceOrdinaryCache entry.value.2 (mergedCache parameter table finalCache)) := by
  intro hwitness
  rcases hwitness with ⟨f, digest, tree, hf, hdigest, hadmissible, huncovered, hsecret, _⟩
  rw [OtsProbeSimulation.ordinaryQueryCache_replaceOrdinaryCache] at hf huncovered
  obtain ⟨value, hrevealed⟩ := jointRetainedDetailed_hit_revealed parameter root table adversary q forgery log verified
    finalState finalCache entry f hf hvalue hresult digest tree hdigest hadmissible hsecret
  exact huncovered (jointRetainedDetailed_revealed_covered
    ⟨parameter, root, OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable (fun _ => 0)),
      fun index tree leaf => table (index, tree, leaf)⟩
    table adversary q forgery log verified finalState finalCache entry f hf hvalue hresult _ value hrevealed)

theorem jointRetainedDetailed_witness_implies_hit
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat)
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (NativeStepResult (Option RetainedGameResult) × SplitHashCache))
    (hresult : result ∈ support (jointRetainedDetailed adversary parameter table q))
    (hwitness : NativeRetainedFtsWitnessEvent parameter table (projectNativeStepCache parameter table result)) :
    result.hit = true := by
  cases result with
  | stopped hit =>
      simp [NativeRetainedFtsWitnessEvent, projectNativeStepCache, OtsProbeSimulation.historyPrefixValue] at hwitness
  | done hit state result =>
      cases hit with
      | true => rfl
      | false =>
          rcases result with ⟨entry, cache⟩
          cases entry with
          | none =>
              simp [NativeRetainedFtsWitnessEvent, projectNativeStepCache, OtsProbeSimulation.historyPrefixValue] at hwitness
          | some entry =>
              rcases hwitness with ⟨value, hvalue, hwitness⟩
              simp only [projectNativeStepCache, Option.map_some, OtsProbeSimulation.historyPrefixValue,
                OtsProbeSimulation.replaceHistoryOrdinaryCache, flattenRetainedCache] at hvalue
              cases hretained : entry.value.1 with
              | none => simp [hretained] at hvalue
              | some retained =>
                  rcases retained with ⟨root, ⟨⟨forgery, log⟩, verified⟩⟩
                  simp only [hretained, Option.map_some, Option.some.injEq] at hvalue
                  subst value
                  exact False.elim (jointRetainedDetailed_no_uncovered_value adversary parameter table q state cache entry
                    root forgery log verified hretained hresult hwitness)

noncomputable def jointRetainedFtsHitRisk
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat) : ENNReal :=
  Pr[fun result => result.hit = true | jointRetainedDetailed adversary parameter table q]

theorem jointRetainedFtsWitnessRisk_eq_hit
    (adversary : Adversary) (parameter : PublicParameter) (table : Coordinate → Digest) (q : Nat) :
    jointRetainedFtsWitnessRisk adversary parameter table q = jointRetainedFtsHitRisk adversary parameter table q := by
  apply probEvent_congr' _ rfl
  intro result hresult
  exact ⟨fun hevent => hevent.elim id (jointRetainedDetailed_witness_implies_hit adversary parameter table q result hresult), Or.inl⟩

end SphincsSecurity.Concrete.FtsProbeSimulation

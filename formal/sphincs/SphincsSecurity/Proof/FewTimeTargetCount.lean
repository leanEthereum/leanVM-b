import SphincsSecurity.Proof.FewTimeTargetSource
import SphincsSecurity.Proof.FewTimePrehit

/-!
# Counting fresh target-view candidates

A direct hash interval contributes its queried input. A successful signer interval contributes the
message-digest input selected by its returned signature. If that input was fresh, distinct
candidate intervals embed into distinct entries of the final random-oracle cache.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def targetCandidateInput?
    (secretKey : SecretKey) (entry : AdversaryCacheEntry) : Option HashInput := by
  rcases entry with ⟨input, output, initialCache, finalCache⟩
  rcases input with worldInput | request
  · rcases worldInput with uniformInput | hashInput
    · exact none
    · exact some hashInput
  · cases output with
    | none => exact none
    | some signature =>
        exact some (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root request signature.randomness))

def FreshTargetCandidate (secretKey : SecretKey)
    (entry : AdversaryCacheEntry) : Prop :=
  ∃ input output,
    targetCandidateInput? secretKey entry = some input
      ∧ entry.initialCache input = none
      ∧ entry.finalCache input = some output

noncomputable instance (secretKey : SecretKey) :
    DecidablePred (FreshTargetCandidate secretKey) :=
  fun entry => Classical.propDecidable (FreshTargetCandidate secretKey entry)

noncomputable def freshTargetCandidatePositions
    (secretKey : SecretKey) (trace : FullAdversaryTrace) :
    Finset (Fin trace.intervals.length) :=
  Finset.univ.filter fun position =>
    FreshTargetCandidate secretKey (trace.intervals.get position)

theorem freshTargetCandidatePositions_card_le_enncard
    (secretKey : SecretKey) (trace : FullAdversaryTrace)
    (finalCache : QueryCache HashSpec)
    (hintervals : trace.IntervalsLe finalCache)
    (hchronological : FullAdversaryTrace.Chronological trace.intervals) :
    ((freshTargetCandidatePositions secretKey trace).card : ℝ≥0∞) ≤
      QueryCache.enncard finalCache := by
  classical
  let candidates := freshTargetCandidatePositions secretKey trace
  let candidateInput : ↑candidates → HashInput := fun candidate =>
    Classical.choose ((Finset.mem_filter.mp candidate.2).2)
  let candidateOutput : ∀ candidate : ↑candidates, HashOutput := fun candidate =>
    Classical.choose (Classical.choose_spec ((Finset.mem_filter.mp candidate.2).2))
  have candidateSpec : ∀ candidate : ↑candidates,
      targetCandidateInput? secretKey (trace.intervals.get candidate.1) =
          some (candidateInput candidate)
        ∧ (trace.intervals.get candidate.1).initialCache (candidateInput candidate) = none
        ∧ (trace.intervals.get candidate.1).finalCache (candidateInput candidate) =
          some (candidateOutput candidate) := by
    intro candidate
    exact Classical.choose_spec
      (Classical.choose_spec ((Finset.mem_filter.mp candidate.2).2))
  let cacheEmbedding : ↑candidates ↪ finalCache.toSet :=
    ⟨fun candidate => ⟨⟨candidateInput candidate, candidateOutput candidate⟩,
        (hintervals (trace.intervals.get candidate.1)
          (List.get_mem trace.intervals candidate.1)).2 (candidateSpec candidate).2.2⟩,
      by
        intro left right heq
        have hinput : candidateInput left = candidateInput right :=
          congrArg (fun entry : finalCache.toSet => entry.1.1) heq
        apply Subtype.ext
        by_contra hposition
        rcases lt_or_gt_of_ne hposition with hlt | hlt
        · have hle := hchronological.get_finalCache_le_initialCache left.1 right.1 hlt
          have hcached := hle (candidateSpec left).2.2
          rw [hinput, (candidateSpec right).2.1] at hcached
          simp at hcached
        · have hle := hchronological.get_finalCache_le_initialCache right.1 left.1 hlt
          have hcached := hle (candidateSpec right).2.2
          rw [← hinput, (candidateSpec left).2.1] at hcached
          simp at hcached⟩
  have hencard := cacheEmbedding.encard_le
  simpa only [candidates, QueryCache.enncard, Set.encard_coe_eq_coe_finsetCard,
    ENat.toENNReal_coe] using ENat.toENNReal_mono hencard

theorem gameAfterSecretsWithViewTrace_freshTargetCandidatePositions_card_le
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret)) :
    ((freshTargetCandidatePositions
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ result.2.trace).card : ℝ≥0∞) ≤ q := by
  have hbase : (result.1, result.2.base) ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
    rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
      support_map]
    exact ⟨result, hresult, rfl⟩
  have hinvariants := gameAfterSecretsWithFullTrace_support_interval_invariants adversary
    parameter otsSecret ftsSecret (result.1, result.2.base) hbase
  calc
    _ ≤ QueryCache.enncard result.2.cache :=
      freshTargetCandidatePositions_card_le_enncard
        ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ result.2.trace result.2.cache
        hinvariants.2.1 hinvariants.2.2
    _ ≤ q := gameAfterSecretsWithFullTrace_support_enncard_le adversary q hq
      parameter hparameter otsSecret hots ftsSecret hfts (result.1, result.2.base) hbase

end SphincsSecurity.Concrete

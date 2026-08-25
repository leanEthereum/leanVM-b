import SphincsSecurity.Proof.FewTimeSource
import SphincsSecurity.Proof.FewTimePrehit

/-!
# Query-budget bound for direct few-time sources

Distinct selected prehits have distinct fresh direct-query inputs. Embedding those inputs into the
final random-oracle cache bounds their number by the complete experiment's hash-query budget.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem FewTimeCover.precachedEntryCount_le_queryBudget
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (result : (Digest × Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hresult : result ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.1.AgreesWithFn f)
    (index : Index) (targetLeaves : DigestTree → FtsLeaf)
    (cover : FewTimeCover f result.2.1
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
      result.2.2.signing.toSigningLog index targetLeaves) :
    ((cover.precachedEntryFinset result.2.2.signing rfl).card : ℝ≥0∞) ≤ q := by
  classical
  obtain ⟨source, _selected, output, hsourceInjective, hsource⟩ :=
    cover.precached_entries_have_injective_fresh_direct_view_sources adversary parameter
      otsSecret ftsSecret result hresult f hf index targetLeaves
  let precached := cover.precachedEntryFinset result.2.2.signing rfl
  let asPrecached : ↑precached → cover.PrecachedEntries result.2.2.signing rfl :=
    fun entry => ⟨entry.1, by
      have hmem : entry.1 ∈ cover.precachedEntryFinset result.2.2.signing rfl := by
        simpa only [precached] using entry.2
      exact (Finset.mem_filter.mp hmem).2⟩
  have hintervals := gameAfterSecretsWithFullTrace_support_interval_invariants adversary
    parameter otsSecret ftsSecret result hresult
  let cacheEmbedding : ↑precached ↪ result.2.1.toSet :=
    ⟨fun entry =>
        let selected := asPrecached entry
        let interval := result.2.2.intervals.get (source selected)
        ⟨⟨cover.entryDigestInput selected.1, output selected⟩, by
          have hcached : interval.finalCache (cover.entryDigestInput selected.1) =
              some (output selected) :=
            randomOracle_run_output_cached (cover.entryDigestInput selected.1)
              interval.initialCache interval.finalCache (output selected)
                (hsource selected).2.2.2.2.2.1
          exact (hintervals.2.1 interval (List.get_mem _ (source selected))).2 hcached⟩,
      by
        intro left right heq
        apply Subtype.ext
        apply cover.entryDigestInput_injective
        have hinput := congrArg
          (fun entry : result.2.1.toSet => entry.1.1) heq
        change cover.entryDigestInput (asPrecached left).1 =
          cover.entryDigestInput (asPrecached right).1 at hinput
        exact hinput⟩
  have hencard := cacheEmbedding.encard_le
  have hcache : QueryCache.enncard result.2.1 ≤ q :=
    gameAfterSecretsWithFullTrace_support_enncard_le adversary q hq parameter hparameter
      otsSecret hots ftsSecret hfts result hresult
  calc
    (precached.card : ℝ≥0∞) ≤ QueryCache.enncard result.2.1 := by
      simpa only [QueryCache.enncard, Set.encard_coe_eq_coe_finsetCard,
        ENat.toENNReal_coe] using ENat.toENNReal_mono hencard
    _ ≤ q := hcache

end SphincsSecurity.Concrete

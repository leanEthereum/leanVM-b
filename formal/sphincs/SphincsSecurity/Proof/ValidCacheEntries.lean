import SphincsSecurity.Proof.ValidDigestCollisionCount
import SphincsSecurity.Proof.RomQueryCharge

namespace SphincsSecurity

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def validCacheEntries (cache : QueryCache HashSpec) : Finset (HashInput × Digest) :=
  if hfinite : Finite cache then
    (((show {input | cache input ≠ none}.Finite from hfinite).toFinset.filter fun input =>
      TargetSum.ValidDigest (truncateHash (fromCache cache input))).image fun input =>
        (input, truncateHash (fromCache cache input)))
  else ∅

theorem mem_validCacheEntries_iff {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {input : HashInput} {digest : Digest} :
    (input, digest) ∈ validCacheEntries cache ↔
      cache input ≠ none ∧ TargetSum.ValidDigest (truncateHash (fromCache cache input)) ∧
        digest = truncateHash (fromCache cache input) := by
  rw [validCacheEntries, dif_pos hfinite, Finset.mem_image]
  constructor
  · rintro ⟨candidate, hc, heq⟩
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hc
    have he : candidate = input := congrArg Prod.fst heq
    subst candidate
    exact ⟨hc.1, hc.2, (congrArg Prod.snd heq).symm⟩
  · rintro ⟨hc, hv, rfl⟩
    exact ⟨input, by simpa only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using And.intro hc hv, rfl⟩

theorem validCacheEntries_fresh {cache : QueryCache HashSpec} (hfinite : Finite cache) {input : HashInput}
    (hfresh : cache input = none) : ∀ entry ∈ validCacheEntries cache, entry.1 ≠ input := by
  rintro ⟨other, digest⟩ hmem heq
  have h := (mem_validCacheEntries_iff hfinite).mp hmem
  change other = input at heq
  subst other
  exact h.1 hfresh

theorem validCacheEntries_cacheQuery {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {input : HashInput} (output : HashOutput) (hfresh : cache input = none) :
    validCacheEntries (cache.cacheQuery input output) = insertValidDigest (validCacheEntries cache) input output := by
  ext ⟨other, digest⟩
  rw [mem_validCacheEntries_iff (finite_cacheQuery hfinite input output), insertValidDigest]
  by_cases hother : other = input
  · subst other
    have hold : (input, digest) ∉ validCacheEntries cache := fun hm =>
      ((mem_validCacheEntries_iff hfinite).mp hm).1 hfresh
    by_cases hv : TargetSum.ValidDigest (truncateHash output)
    · simp [hold, QueryCache.cacheQuery_self, fromCache, hv, eq_comm]
    · simp [hold, QueryCache.cacheQuery_self, fromCache, hv]
  · have hfrom : fromCache (cache.cacheQuery input output) other = fromCache cache other := by
      simp only [fromCache, QueryCache.cacheQuery_of_ne _ _ hother]
    by_cases hv : TargetSum.ValidDigest (truncateHash output)
    · simp only [if_pos hv, Finset.mem_insert, Prod.mk.injEq, hother, false_and, false_or,
        mem_validCacheEntries_iff hfinite, QueryCache.cacheQuery_of_ne _ _ hother, hfrom]
    · simp only [if_neg hv, mem_validCacheEntries_iff hfinite, QueryCache.cacheQuery_of_ne _ _ hother, hfrom]

@[simp] theorem validCacheEntries_empty : validCacheEntries ∅ = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨input, digest⟩ hmem
  exact ((mem_validCacheEntries_iff finite_empty).mp hmem).1 rfl

end SphincsSecurity

import SphincsSecurity.Proof.EncodingMessageReserve

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable

theorem encodingMessageReserve_cacheQuery_eq_increment
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {key : SecretKey}
    {input : HashInput} {answer : HashOutput} {queried : EncodingPosition}
    (hfresh : cache input = none) (hat : AtEncodingPosition key.parameter input queried) :
    encodingMessageReserve (cache.cacheQuery input answer) key =
      encodingMessageReserve cache key + encodingMessageIncrement cache key queried := by
  have hsettled (position : EncodingPosition) :
      EncodingMessageSettledAt (cache.cacheQuery input answer) key position ↔
        EncodingMessageSettledAt cache key position :=
    ⟨fun h => h.of_cacheQuery_of_atEncoding hfresh hat,
      fun h => h.mono (le_cacheQuery (answer := answer) hfresh)⟩
  have hpoint (position : EncodingPosition) :
      encodingMessageReserveAt (cache.cacheQuery input answer) key position =
        encodingMessageReserveAt cache key position +
          if position = queried then encodingMessageIncrement cache key queried else 0 := by
    by_cases heq : position = queried
    · subst position
      simp only [encodingMessageReserveAt, hsettled, encodingMessageIncrement, if_true]
      by_cases hs : EncodingMessageSettledAt cache key queried
      · simp only [if_pos hs, Nat.zero_add]
      · simp only [if_neg hs, encodingCachedAt_cacheQuery_self hat]
        apply Set.ncard_insert_of_notMem _ (encodingCachedAt_finite hfinite queried)
        intro hmem
        exact hmem.1 hfresh
    · simp only [encodingMessageReserveAt, hsettled, if_neg heq, Nat.add_zero]
      rw [encodingCachedAt_cacheQuery_of_not_atPosition
        (answer := answer) (fun h => heq (atEncodingPosition_unique h hat))]
  simp only [encodingMessageReserve, hpoint, Finset.sum_add_distrib, Fintype.sum_ite_eq']

theorem encodingMessageReserve_le_cachedInputs {cache : QueryCache HashSpec}
    (hfinite : Finite cache) (key : SecretKey) :
    encodingMessageReserve cache key ≤ {input | cache input ≠ none}.ncard := by
  apply le_trans _ (sum_encodingCachedAt_ncard_le (parameter := key.parameter) hfinite)
  unfold encodingMessageReserve
  apply Finset.sum_le_sum
  intro position _
  unfold encodingMessageReserveAt
  split_ifs
  · exact Nat.zero_le _
  · exact le_rfl

end SphincsSecurity.Concrete

import SphincsSecurity.Proof.EncodingLatent
import SphincsSecurity.Proof.EncodingSelection

/-!
# Cache-derived encoding selection risk

The abstract conditional-selection schedule is instantiated with the concrete encoding inputs at
one structural position and one settled layer message. Every cached candidate retains its full hash
input as the identifier used to exclude the selected input itself.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 100000

def encodingRetryInput (parameter : PublicParameter) (position : EncodingPosition)
    (message : Digest) (counter : Nat) : HashInput :=
  tweakableHashInput parameter position.domain
    (digestBytes message ++ counterBytes (BitVec.ofNat counterBits counter))

noncomputable def encodingRetryScheduleFrom
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (position : EncodingPosition) (message : Digest) :
    Nat → Nat → List (HashInput × Option Digest)
  | 0, _ => []
  | attempts + 1, counter =>
      let input := encodingRetryInput parameter position message counter
      (input, (cache input).map truncateHash) ::
        encodingRetryScheduleFrom parameter cache position message attempts (counter + 1)

noncomputable def encodingRetrySchedule
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (position : EncodingPosition) (message : Digest) :
    List (HashInput × Option Digest) :=
  encodingRetryScheduleFrom parameter cache position message encodingAttemptLimit 0

theorem encodingRetryInput_injective_of_lt
    {parameter : PublicParameter} {position : EncodingPosition} {message : Digest}
    {left right : Nat} (hleft : left < encodingAttemptLimit)
    (hright : right < encodingAttemptLimit)
    (heq : encodingRetryInput parameter position message left =
      encodingRetryInput parameter position message right) :
    left = right := by
  have hpayload :=
    (tweakableHashInput_injective parameter (by trivial) (by trivial) heq).2
  obtain ⟨_, hcounter⟩ :=
    List.append_inj hpayload (by simp [digestBytes_length])
  apply ofNat_inj_of_lt (w := counterBits)
    (by simpa [encodingAttemptLimit, counterBits] using hleft)
    (by simpa [encodingAttemptLimit, counterBits] using hright)
  exact bytesLE_injective hcounter

theorem encodingRetryScheduleFrom_add
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (position : EncodingPosition) (message : Digest)
    (first remaining counter : Nat) :
    encodingRetryScheduleFrom parameter cache position message
        (first + remaining) counter =
      encodingRetryScheduleFrom parameter cache position message first counter ++
        encodingRetryScheduleFrom parameter cache position message remaining
          (counter + first) := by
  induction first generalizing counter with
  | zero => simp [encodingRetryScheduleFrom]
  | succ first ih =>
      rw [Nat.succ_add, encodingRetryScheduleFrom, encodingRetryScheduleFrom]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (counter + 1)

theorem encodingRetryScheduleFrom_cacheQuery_of_ne_of_range
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {position : EncodingPosition} {message : Digest}
    {input : HashInput} {answer : HashOutput} {attempts counter : Nat}
    (hne : ∀ candidate : Nat, counter ≤ candidate → candidate < counter + attempts →
      input ≠ encodingRetryInput parameter position message candidate) :
    encodingRetryScheduleFrom parameter (cache.cacheQuery input answer)
        position message attempts counter =
      encodingRetryScheduleFrom parameter cache position message attempts counter := by
  induction attempts generalizing counter with
  | zero => rfl
  | succ attempts ih =>
      rw [encodingRetryScheduleFrom, encodingRetryScheduleFrom]
      have hcurrent := hne counter (by omega) (by omega)
      rw [QueryCache.cacheQuery_of_ne _ _ hcurrent.symm]
      apply congrArg ((encodingRetryInput parameter position message counter,
        (cache (encodingRetryInput parameter position message counter)).map truncateHash) :: ·)
      apply ih
      intro candidate hlower hupper
      apply hne candidate (by omega)
      omega

theorem encodingRetrySchedule_eq_split
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {position : EncodingPosition} {message : Digest}
    {counter : Nat} (hcounter : counter < encodingAttemptLimit) :
    encodingRetrySchedule parameter cache position message =
      encodingRetryScheduleFrom parameter cache position message counter 0 ++
        (encodingRetryInput parameter position message counter,
          (cache (encodingRetryInput parameter position message counter)).map truncateHash) ::
        encodingRetryScheduleFrom parameter cache position message
          (encodingAttemptLimit - (counter + 1)) (counter + 1) := by
  rw [encodingRetrySchedule]
  conv_lhs =>
    rw [show encodingAttemptLimit = counter +
        (1 + (encodingAttemptLimit - (counter + 1))) by omega]
  rw [encodingRetryScheduleFrom_add]
  rw [show 1 + (encodingAttemptLimit - (counter + 1)) =
    (encodingAttemptLimit - (counter + 1)) + 1 by omega,
    encodingRetryScheduleFrom]
  rw [show 0 + counter = counter by omega]

theorem encodingRetrySchedule_eq_split_of_uncached
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {position : EncodingPosition} {message : Digest}
    {counter : Nat} (hcounter : counter < encodingAttemptLimit)
    (huncached : cache (encodingRetryInput parameter position message counter) = none) :
    encodingRetrySchedule parameter cache position message =
      encodingRetryScheduleFrom parameter cache position message counter 0 ++
        (encodingRetryInput parameter position message counter, none) ::
        encodingRetryScheduleFrom parameter cache position message
          (encodingAttemptLimit - (counter + 1)) (counter + 1) := by
  rw [encodingRetrySchedule_eq_split hcounter, huncached]
  rfl

theorem encodingRetrySchedule_cacheQuery_eq_split
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {position : EncodingPosition} {message : Digest}
    {counter : Nat} (hcounter : counter < encodingAttemptLimit)
    (answer : HashOutput) :
    encodingRetrySchedule parameter
        (cache.cacheQuery (encodingRetryInput parameter position message counter) answer)
        position message =
      encodingRetryScheduleFrom parameter cache position message counter 0 ++
        (encodingRetryInput parameter position message counter,
          some (truncateHash answer)) ::
        encodingRetryScheduleFrom parameter cache position message
          (encodingAttemptLimit - (counter + 1)) (counter + 1) := by
  rw [encodingRetrySchedule_eq_split hcounter]
  have hprefix := encodingRetryScheduleFrom_cacheQuery_of_ne_of_range
    (parameter := parameter) (cache := cache) (position := position) (message := message)
    (input := encodingRetryInput parameter position message counter) (answer := answer)
    (attempts := counter) (counter := 0) (by
      intro candidate _ hcandidate heq
      have hsame := encodingRetryInput_injective_of_lt
        hcounter (by omega) heq
      omega)
  have hsuffix := encodingRetryScheduleFrom_cacheQuery_of_ne_of_range
    (parameter := parameter) (cache := cache) (position := position) (message := message)
    (input := encodingRetryInput parameter position message counter) (answer := answer)
    (attempts := encodingAttemptLimit - (counter + 1)) (counter := counter + 1) (by
      intro candidate hlower hcandidate heq
      have hcandidateLt : candidate < encodingAttemptLimit := by omega
      have hsame := encodingRetryInput_injective_of_lt
        hcounter hcandidateLt heq
      omega)
  rw [hprefix, hsuffix, QueryCache.cacheQuery_self]
  rfl

theorem encodingRetryScheduleFrom_invalidPrefix
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {position : EncodingPosition} {message : Digest}
    {attempts counter : Nat}
    (hcached : ∀ candidate : Nat, counter ≤ candidate → candidate < counter + attempts →
      cache (encodingRetryInput parameter position message candidate) ≠ none)
    (hinvalid : ∀ candidate : Nat, counter ≤ candidate → candidate < counter + attempts →
      ¬ TargetSum.ValidDigest (truncateHash (fromCache cache
        (encodingRetryInput parameter position message candidate)))) :
    EncodingSelection.InvalidPrefix
      (encodingRetryScheduleFrom parameter cache position message attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact .nil
  | succ attempts ih =>
      rw [encodingRetryScheduleFrom]
      have hcurrentCached := hcached counter (by omega) (by omega)
      cases hanswer : cache (encodingRetryInput parameter position message counter) with
      | none => exact (hcurrentCached hanswer).elim
      | some answer =>
          apply EncodingSelection.InvalidPrefix.cons
          · simpa only [fromCache, hanswer, Option.getD_some] using
              hinvalid counter (by omega) (by omega)
          · apply ih
            · intro candidate hlower hupper
              apply hcached candidate (by omega)
              omega
            · intro candidate hlower hupper
              apply hinvalid candidate (by omega)
              omega

theorem encodingRetryScheduleFrom_zero_invalidPrefix
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {position : EncodingPosition} {message : Digest}
    {counter : Nat}
    (hcached : ∀ candidate : Nat, candidate < counter →
      cache (encodingRetryInput parameter position message candidate) ≠ none)
    (hinvalid : ∀ candidate : Nat, candidate < counter →
      ¬ TargetSum.ValidDigest (truncateHash (fromCache cache
        (encodingRetryInput parameter position message candidate)))) :
    EncodingSelection.InvalidPrefix
      (encodingRetryScheduleFrom parameter cache position message counter 0) := by
  apply encodingRetryScheduleFrom_invalidPrefix
  · intro candidate _ hcandidate
    exact hcached candidate (by simpa using hcandidate)
  · intro candidate _ hcandidate
    exact hinvalid candidate (by simpa using hcandidate)

theorem encodingSearchFrom_before_mem (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (position : EncodingPosition) (message : Digest)
    (attempts counter : Nat) (selected : Counter)
    (hbound : counter + attempts ≤ 2 ^ counterBits)
    (hselected : evalWithAnswerFn f
      (encodingSearchFrom parameter position.lay position.tree position.leafIdx
        message attempts counter) = some selected)
    (candidate : Nat) (hlower : counter ≤ candidate)
    (hbefore : candidate < selected.toNat) :
    encodingRetryInput parameter position message candidate ∈
      queriedInputs f
        (encodingSearchFrom parameter position.lay position.tree position.leafIdx
          message attempts counter) := by
  induction attempts generalizing counter candidate with
  | zero => simp [encodingSearchFrom] at hselected
  | succ attempts ih =>
      have hcounterLt : counter < 2 ^ counterBits := by omega
      rw [encodingSearchFrom, evalWithAnswerFn_bind] at hselected
      cases hencode : evalWithAnswerFn f
          (encode parameter position.lay position.tree position.leafIdx message
            (BitVec.ofNat counterBits counter)) with
      | none =>
          simp only [hencode] at hselected
          rw [encodingSearchFrom, queriedInputs_bind]
          by_cases heq : candidate = counter
          · subst candidate
            apply List.mem_append_left
            simp only [encode, queriedInputs_bind, queriedInputs_tweakableHash,
              queriedInputs_pure, List.append_nil, List.mem_singleton]
            rfl
          · apply List.mem_append_right
            simp only [hencode]
            exact ih (counter + 1) (by omega) hselected candidate (by omega) hbefore
      | some codeword =>
          have hselectedEq : BitVec.ofNat counterBits counter = selected := by
            simpa only [hencode, evalWithAnswerFn_pure, Option.some.injEq] using hselected
          have hselectedNat : selected.toNat = counter := by
            rw [← hselectedEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcounterLt]
          omega

theorem encodingSearch_before_mem (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (position : EncodingPosition) (message : Digest)
    (selected : Counter)
    (hselected : evalWithAnswerFn f
      (encodingSearch parameter position.lay position.tree position.leafIdx message) =
        some selected)
    (candidate : Nat) (hbefore : candidate < selected.toNat) :
    encodingRetryInput parameter position message candidate ∈
      queriedInputs f
        (encodingSearch parameter position.lay position.tree position.leafIdx message) := by
  exact encodingSearchFrom_before_mem f parameter position message encodingAttemptLimit 0
    selected (by norm_num [encodingAttemptLimit, counterBits])
    (by simpa only [encodingSearch] using hselected) candidate (by omega) hbefore

theorem encodingSearch_before_cached
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {position : EncodingPosition} {message : Digest} {selected : Counter}
    (hselected : evalWithAnswerFn (fromCache cache)
      (encodingSearch parameter position.lay position.tree position.leafIdx message) =
        some selected)
    (hrun : CachedRun cache (fromCache cache)
      (encodingSearch parameter position.lay position.tree position.leafIdx message))
    {candidate : Nat} (hbefore : candidate < selected.toNat) :
    cache (encodingRetryInput parameter position message candidate) ≠ none := by
  exact hrun _ (encodingSearch_before_mem (fromCache cache) parameter position message
    selected hselected candidate hbefore)

theorem encodingRetryScheduleFrom_cacheQuery_of_ne
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {position : EncodingPosition} {message : Digest}
    {input : HashInput} {answer : HashOutput}
    (hne : ∀ counter : Nat,
      input ≠ encodingRetryInput parameter position message counter) :
    ∀ attempts counter,
      encodingRetryScheduleFrom parameter (cache.cacheQuery input answer)
          position message attempts counter =
        encodingRetryScheduleFrom parameter cache position message attempts counter := by
  intro attempts
  induction attempts with
  | zero => intro counter; rfl
  | succ attempts ih =>
      intro counter
      rw [encodingRetryScheduleFrom, encodingRetryScheduleFrom]
      have hother : encodingRetryInput parameter position message counter ≠ input :=
        (hne counter).symm
      rw [QueryCache.cacheQuery_of_ne _ _ hother, ih (counter + 1)]

theorem encodingRetrySchedule_cacheQuery_of_ne
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {position : EncodingPosition} {message : Digest}
    {input : HashInput} {answer : HashOutput}
    (hne : ∀ counter : Nat,
      input ≠ encodingRetryInput parameter position message counter) :
    encodingRetrySchedule parameter (cache.cacheQuery input answer) position message =
      encodingRetrySchedule parameter cache position message := by
  exact encodingRetryScheduleFrom_cacheQuery_of_ne hne encodingAttemptLimit 0

theorem encodingRetrySchedule_cacheQuery_of_ne_of_lt
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {position : EncodingPosition} {message : Digest}
    {input : HashInput} {answer : HashOutput}
    (hne : ∀ counter : Nat, counter < encodingAttemptLimit →
      input ≠ encodingRetryInput parameter position message counter) :
    encodingRetrySchedule parameter (cache.cacheQuery input answer) position message =
      encodingRetrySchedule parameter cache position message := by
  rw [encodingRetrySchedule]
  apply encodingRetryScheduleFrom_cacheQuery_of_ne_of_range
  intro candidate _ hcandidate
  exact hne candidate (by simpa using hcandidate)

noncomputable def encodingSelectionCandidates
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (position : EncodingPosition) :
    Finset (HashInput × Digest) :=
  open Classical in
  (((encodingCachedAt_finite (parameter := parameter) (cache := cache)
      hfinite position).toFinset.filter fun input =>
        TargetSum.ValidDigest (truncateHash (fromCache cache input))).image fun input =>
          (input, truncateHash (fromCache cache input)))

noncomputable def encodingConditionalRiskAtMessage
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (position : EncodingPosition)
    (message : Digest) : ℝ≥0∞ :=
  EncodingSelection.selectionRisk
    (encodingRetrySchedule parameter cache position message)
    (encodingSelectionCandidates parameter cache hfinite position)

theorem mem_encodingSelectionCandidates_iff
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    (hfinite : Finite cache) {position : EncodingPosition}
    {input : HashInput} {digest : Digest} :
    (input, digest) ∈ encodingSelectionCandidates parameter cache hfinite position ↔
      cache input ≠ none
        ∧ AtEncodingPosition parameter input position
        ∧ TargetSum.ValidDigest (truncateHash (fromCache cache input))
        ∧ digest = truncateHash (fromCache cache input) := by
  classical
  rw [encodingSelectionCandidates, Finset.mem_image]
  constructor
  · rintro ⟨candidate, hcandidate, hpairs⟩
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hcandidate
    have hinput : candidate = input := congrArg Prod.fst hpairs
    subst candidate
    exact ⟨hcandidate.1.1, hcandidate.1.2, hcandidate.2,
      (congrArg Prod.snd hpairs).symm⟩
  · rintro ⟨hcached, hposition, hvalid, rfl⟩
    exact ⟨input, by
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨⟨hcached, hposition⟩, hvalid⟩, rfl⟩

theorem encodingSelectionCandidates_cacheQuery_self
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    (hfinite : Finite cache) {position : EncodingPosition}
    {input : HashInput} {answer : HashOutput}
    (huncached : cache input = none)
    (hposition : AtEncodingPosition parameter input position) :
    encodingSelectionCandidates parameter (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) position =
      EncodingSelection.candidateTargets input
        (encodingSelectionCandidates parameter cache hfinite position) answer := by
  classical
  ext candidate
  obtain ⟨candidateInput, candidateDigest⟩ := candidate
  rw [mem_encodingSelectionCandidates_iff]
  by_cases hvalid : TargetSum.ValidDigest (truncateHash answer)
  · rw [EncodingSelection.candidateTargets, if_pos hvalid, Finset.mem_insert]
    constructor
    · intro hcandidate
      by_cases heq : candidateInput = input
      · subst candidateInput
        apply Or.inl
        have hdigest : candidateDigest = truncateHash answer := by
          simpa [fromCache, QueryCache.cacheQuery_self] using hcandidate.2.2.2
        rw [hdigest]
      · apply Or.inr
        rw [mem_encodingSelectionCandidates_iff]
        simpa [fromCache, QueryCache.cacheQuery_of_ne _ _ heq] using hcandidate
    · rintro (heq | hcandidate)
      · have hinput : candidateInput = input := congrArg Prod.fst heq
        have hdigest : candidateDigest = truncateHash answer := congrArg Prod.snd heq
        subst candidateInput
        subst candidateDigest
        exact ⟨by simp, hposition, by
          simpa [fromCache, QueryCache.cacheQuery_self] using hvalid, by
          simp [fromCache, QueryCache.cacheQuery_self]⟩
      · rw [mem_encodingSelectionCandidates_iff] at hcandidate
        have hne : candidateInput ≠ input := by
          intro heq
          subst candidateInput
          exact hcandidate.1 huncached
        simpa [fromCache, QueryCache.cacheQuery_of_ne _ _ hne] using hcandidate
  · rw [EncodingSelection.candidateTargets, if_neg hvalid]
    rw [mem_encodingSelectionCandidates_iff]
    constructor
    · intro hcandidate
      have hne : candidateInput ≠ input := by
        intro heq
        subst candidateInput
        apply hvalid
        simpa [fromCache, QueryCache.cacheQuery_self] using hcandidate.2.2.1
      simpa [fromCache, QueryCache.cacheQuery_of_ne _ _ hne] using hcandidate
    · intro hcandidate
      have hne : candidateInput ≠ input := by
        intro heq
        subst candidateInput
        exact hcandidate.1 huncached
      simpa [fromCache, QueryCache.cacheQuery_of_ne _ _ hne] using hcandidate

theorem uniform_encodingConditionalRiskAtMessage_cacheQuery_of_ne_sum_le
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    (hfinite : Finite cache) {position : EncodingPosition}
    {message : Digest} {input : HashInput}
    (huncached : cache input = none)
    (hposition : AtEncodingPosition parameter input position)
    (hne : ∀ counter : Nat, counter < encodingAttemptLimit →
      input ≠ encodingRetryInput parameter position message counter) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingConditionalRiskAtMessage parameter
          (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer)
          position message) ≤
      encodingConditionalRiskAtMessage parameter cache hfinite position message +
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simp_rw [encodingConditionalRiskAtMessage,
    encodingRetrySchedule_cacheQuery_of_ne_of_lt hne,
    encodingSelectionCandidates_cacheQuery_self hfinite huncached hposition]
  exact EncodingSelection.uniform_candidateTargets_selectionRisk_sum_le input
    (encodingRetrySchedule parameter cache position message)
    (encodingSelectionCandidates parameter cache hfinite position)

theorem uniform_encodingConditionalRiskAtMessage_cacheQuery_at_counter_sum_le
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    (hfinite : Finite cache) {position : EncodingPosition}
    {message : Digest} {counter : Nat}
    (hcounter : counter < encodingAttemptLimit)
    (huncached : cache (encodingRetryInput parameter position message counter) = none) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingConditionalRiskAtMessage parameter
          (cache.cacheQuery (encodingRetryInput parameter position message counter) answer)
          (finite_cacheQuery hfinite
            (encodingRetryInput parameter position message counter) answer)
          position message) ≤
      encodingConditionalRiskAtMessage parameter cache hfinite position message +
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have hposition : AtEncodingPosition parameter
      (encodingRetryInput parameter position message counter) position :=
    ⟨digestBytes message ++ counterBytes (BitVec.ofNat counterBits counter), rfl⟩
  simp only [encodingConditionalRiskAtMessage]
  simp_rw [encodingRetrySchedule_cacheQuery_eq_split hcounter,
    encodingSelectionCandidates_cacheQuery_self hfinite huncached hposition]
  rw [encodingRetrySchedule_eq_split_of_uncached hcounter huncached]
  exact EncodingSelection.uniform_reveal_append_candidate_sum_le
    (encodingRetryScheduleFrom parameter cache position message counter 0)
    (encodingRetryInput parameter position message counter)
    (encodingRetryScheduleFrom parameter cache position message
      (encodingAttemptLimit - (counter + 1)) (counter + 1))
    (encodingSelectionCandidates parameter cache hfinite position)

theorem uniform_encodingConditionalRiskAtMessage_cacheQuery_sum_le
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    (hfinite : Finite cache) {position : EncodingPosition}
    {message : Digest} {input : HashInput}
    (huncached : cache input = none)
    (hposition : AtEncodingPosition parameter input position) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingConditionalRiskAtMessage parameter
          (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer)
          position message) ≤
      encodingConditionalRiskAtMessage parameter cache hfinite position message +
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  classical
  by_cases hretry : ∃ counter : Nat, counter < encodingAttemptLimit ∧
      input = encodingRetryInput parameter position message counter
  · obtain ⟨counter, hcounter, heq⟩ := hretry
    subst input
    exact uniform_encodingConditionalRiskAtMessage_cacheQuery_at_counter_sum_le
      hfinite hcounter huncached
  · apply uniform_encodingConditionalRiskAtMessage_cacheQuery_of_ne_sum_le
      hfinite huncached hposition
    intro counter hcounter heq
    exact hretry ⟨counter, hcounter, heq⟩

@[simp] theorem encodingSelectionCandidates_empty
    (parameter : PublicParameter) (position : EncodingPosition) :
    encodingSelectionCandidates parameter ∅ finite_empty position = ∅ := by
  ext candidate
  obtain ⟨input, digest⟩ := candidate
  rw [mem_encodingSelectionCandidates_iff]
  simp

@[simp] theorem encodingConditionalRiskAtMessage_empty
    (parameter : PublicParameter) (position : EncodingPosition)
    (message : Digest) :
    encodingConditionalRiskAtMessage parameter ∅ finite_empty position message = 0 := by
  rw [encodingConditionalRiskAtMessage, encodingSelectionCandidates_empty,
    EncodingSelection.selectionRisk_empty_targets]

end SphincsSecurity.Concrete

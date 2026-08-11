import XmssSecurity.SuffixEventProbability

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable def OutcomeChainValueRevealed (cache : QueryCache HashSpec)
    (outcome : GameOutcome) (chain : ChainIndex) : Prop :=
  outcome.verified = true ∧
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter
          outcome.forgery.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness)) = some encoding ∧
      outcome.forgery.signature.chainValue chain =
        Wots.signChain
          (Concrete.CacheView.chainStep cache outcome.secretKey.parameter
            outcome.forgery.epoch chain)
          (encoding chain) (outcome.secretKey.chainStart outcome.forgery.epoch chain)

noncomputable def OutcomeChainValueHasKeygenOrigin (keygenCache finalCache : QueryCache HashSpec)
    (secretKey : SecretKey) (outcome : GameOutcome) (chain : ChainIndex) : Prop :=
  outcome.verified = true ∧
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache secretKey.parameter
          outcome.forgery.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness)) = some encoding ∧
      (((encoding chain).val = 0 ∧
          outcome.forgery.signature.chainValue chain =
            secretKey.chainStart outcome.forgery.epoch chain) ∨
        ∃ previous : ChainStep, ∃ output,
          previous.val + 1 = (encoding chain).val ∧
          keygenCache
            (Concrete.CacheView.chainInput secretKey.parameter
              outcome.forgery.epoch chain previous
              (Wots.walk
                (Concrete.CacheView.chainStep keygenCache secretKey.parameter
                  outcome.forgery.epoch chain)
                0 previous.val
                (secretKey.chainStart outcome.forgery.epoch chain))) = some output ∧
          truncateHash output = outcome.forgery.signature.chainValue chain)

noncomputable def OutcomeGuessesKeygenChainValue (keygenCache finalCache : QueryCache HashSpec)
    (secretKey : SecretKey) (outcome : GameOutcome) (chain : ChainIndex) : Prop :=
  outcome.verified = true ∧
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache secretKey.parameter outcome.forgery.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness)) = some encoding ∧
      outcome.forgery.signature.chainValue chain =
        Wots.signChain
          (Concrete.CacheView.chainStep keygenCache secretKey.parameter
            outcome.forgery.epoch chain)
          (encoding chain) (secretKey.chainStart outcome.forgery.epoch chain)

theorem chainValueRevealed_afterKeygen_guesses_keygenValue
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (chain : ChainIndex)
    (hrevealed : OutcomeChainValueRevealed execution.2 execution.1 chain) :
    OutcomeGuessesKeygenChainValue keyResult.2 execution.2 keyResult.1.2 execution.1 chain := by
  obtain ⟨hverified, encoding, hdecode, hvalue⟩ := hrevealed
  have hkeys := detailedGameAfterKeygen_keys_eq adversary keyResult.1.1 keyResult.1.2
    keyResult.2 execution hafter
  rw [hkeys.2] at hdecode hvalue
  have hcacheLe := xmssRom_cache_le
    (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)
    keyResult.2 execution hafter
  have hwalk := Concrete.keygen_chainWalk_eq_of_cache_le keyResult hkeygen execution.2
    hcacheLe execution.1.forgery.epoch chain (encoding chain).val
    (Nat.le_pred_of_lt (encoding chain).isLt)
  refine ⟨hverified, encoding, hdecode, ?_⟩
  exact hvalue.trans (by simpa only [Wots.signChain] using hwalk.symm)

theorem chainValueRevealed_afterKeygen_has_origin
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (chain : ChainIndex)
    (hrevealed : OutcomeChainValueRevealed execution.2 execution.1 chain) :
    OutcomeChainValueHasKeygenOrigin keyResult.2 execution.2 keyResult.1.2 execution.1 chain := by
  obtain ⟨hverified, encoding, hdecode, hvalue⟩ := hrevealed
  have hkeys := detailedGameAfterKeygen_keys_eq adversary keyResult.1.1 keyResult.1.2
    keyResult.2 execution hafter
  rw [hkeys.2] at hdecode hvalue
  have hcacheLe := xmssRom_cache_le
    (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)
    keyResult.2 execution hafter
  have hwalk := Concrete.keygen_chainWalk_eq_of_cache_le keyResult hkeygen execution.2
    hcacheLe execution.1.forgery.epoch chain (encoding chain).val
    (Nat.le_pred_of_lt (encoding chain).isLt)
  refine ⟨hverified, encoding, hdecode, ?_⟩
  by_cases hzero : (encoding chain).val = 0
  · left
    refine ⟨hzero, ?_⟩
    simpa [Wots.signChain, hzero] using hvalue
  · right
    have hpositive : 0 < (encoding chain).val := Nat.pos_of_ne_zero hzero
    obtain ⟨previous, output, hprevious, hcached, houtput⟩ :=
      Concrete.keygen_cache_has_chainValue_preimage keyResult hkeygen
        execution.1.forgery.epoch chain (encoding chain) hpositive
    refine ⟨previous, output, hprevious, ?_, ?_⟩
    · exact hcached
    · calc
        truncateHash output = Wots.signChain
            (Concrete.CacheView.chainStep keyResult.2 keyResult.1.2.parameter
              execution.1.forgery.epoch chain)
            (encoding chain)
            (keyResult.1.2.chainStart execution.1.forgery.epoch chain) := houtput
        _ = Wots.signChain
            (Concrete.CacheView.chainStep execution.2 keyResult.1.2.parameter
              execution.1.forgery.epoch chain)
            (encoding chain)
            (keyResult.1.2.chainStart execution.1.forgery.epoch chain) := hwalk
        _ = execution.1.forgery.signature.chainValue chain := hvalue.symm

theorem chainValueRevealed_afterKeygen_probability_le_origin
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (chain : ChainIndex) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      OutcomeChainValueRevealed execution.2 execution.1 chain |
      (simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2] ≤
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        OutcomeChainValueHasKeygenOrigin keyResult.2 execution.2 keyResult.1.2 execution.1 chain |
        (simulateQ xmssRomImpl
          (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
            keyResult.2] := by
  apply probEvent_mono
  intro execution hafter hrevealed
  exact chainValueRevealed_afterKeygen_has_origin adversary keyResult hkeygen execution
    hafter chain hrevealed

theorem chain_event_afterKeygen_revealed_or_collision
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (chain : ChainIndex)
    (hevent : OutcomeBadEventOccurs execution.2 execution.1 (.chain chain)) :
    OutcomeChainValueRevealed execution.2 execution.1 chain ∨
      Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
        (keygenChainTargetInput keyResult.1.2 keyResult.2) := by
  rcases hevent.2 with hsame | hfresh
  · obtain ⟨request, signature, signedEncoding, forgedEncoding, hsignedDecode,
      hforgedDecode, hreturned, hepoch, hchain⟩ := hsame
    have hgame := afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen
      execution hafter
    have hsignature := detailed_execution_returned_signature_eq adversary execution hgame
      request signature signedEncoding hsignedDecode hreturned
    change Wots.IsBackwardWitnessAt
      (fun candidateChain => Concrete.CacheView.chainStep execution.2
        execution.1.secretKey.parameter request.epoch candidateChain)
      signedEncoding forgedEncoding signature.chainValue
      execution.1.forgery.signature.chainValue chain at hchain
    have hsignedValue : signature.chainValue chain =
        Wots.signChain
          (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
            request.epoch chain)
          (signedEncoding chain) (execution.1.secretKey.chainStart request.epoch chain) := by
      rw [hsignature]
      rfl
    rcases Wots.backwardWitness_eq_honest_or_hasStepCollision
      (fun candidateChain => Concrete.CacheView.chainStep execution.2
        execution.1.secretKey.parameter request.epoch candidateChain)
      signedEncoding forgedEncoding signature.chainValue
      execution.1.forgery.signature.chainValue
      (execution.1.secretKey.chainStart request.epoch) chain hsignedValue hchain with
      hrevealed | hcollision
    · left
      refine ⟨hevent.1, forgedEncoding, ?_, ?_⟩
      · simpa [hepoch] using hforgedDecode
      · simpa [hepoch] using hrevealed
    · right
      obtain ⟨offset, hoffset, hne, heq⟩ := hcollision
      have hposition : offset < chainLength - 1 - (forgedEncoding chain).val := by
        have hsignedLt := (signedEncoding chain).isLt
        have hforgedLe := hchain.1.le
        omega
      let position : TargetSum.SuffixPosition forgedEncoding :=
        ⟨chain, ⟨offset, hposition⟩⟩
      have hsuffix : Wots.IsSuffixCollisionAt
          (fun candidateChain => Concrete.CacheView.chainStep execution.2
            execution.1.secretKey.parameter execution.1.forgery.epoch candidateChain)
          forgedEncoding forgedEncoding
          (fun candidateChain => Wots.signChain
            (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
              execution.1.forgery.epoch candidateChain)
            (forgedEncoding candidateChain)
            (execution.1.secretKey.chainStart execution.1.forgery.epoch candidateChain))
          execution.1.forgery.signature.chainValue position := by
        dsimp only [Wots.IsSuffixCollisionAt, position]
        simp only [Nat.sub_self, Wots.walk_zero]
        exact ⟨le_rfl, by simpa only [hepoch] using hne,
          by simpa only [hepoch] using heq⟩
      have hforgedDecode' : TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
            execution.1.forgery.epoch
            (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
          some forgedEncoding := by
        simpa [hepoch] using hforgedDecode
      exact fresh_suffix_witness_afterKeygen_orientation adversary keyResult hkeygen execution
        hafter forgedEncoding hevent.1 hforgedDecode' position hsuffix
  · left
    obtain ⟨forgedEncoding, _hforgedValid, hforgedDecode, hchain⟩ := hfresh
    refine ⟨hevent.1, forgedEncoding, hforgedDecode, ?_⟩
    exact hchain

theorem chain_outcomeBadEvent_probability_le_revealed_add
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) (chain : ChainIndex) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      OutcomeBadEventOccurs execution.2 execution.1 (.chain chain) |
      detailedGameWithCache Concrete.scheme adversary] ≤
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        OutcomeChainValueRevealed execution.2 execution.1 chain |
        detailedGameWithCache Concrete.scheme adversary] +
        (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  have hdetailedBound :
      (detailedGameCore Concrete.scheme adversary).IsQueryBoundP
        (· matches .inr _) q :=
    (hasHashQueryBound_iff_detailedGameCore Concrete.scheme adversary q).mp hbound
  unfold detailedGameCore at hdetailedBound
  unfold detailedGameWithCache detailedGameCore
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum,
    probEvent_bind_eq_tsum]
  calc
    ∑' keyResult,
        Pr[= keyResult | (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅] *
          Pr[fun execution : GameOutcome × QueryCache HashSpec =>
            OutcomeBadEventOccurs execution.2 execution.1 (.chain chain) |
            (simulateQ xmssRomImpl
              (detailedGameAfterKeygen Concrete.scheme adversary
                keyResult.1.1 keyResult.1.2)).run keyResult.2] ≤
      ∑' keyResult,
        Pr[= keyResult | (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅] *
          (Pr[fun execution : GameOutcome × QueryCache HashSpec =>
              OutcomeChainValueRevealed execution.2 execution.1 chain |
              (simulateQ xmssRomImpl
                (detailedGameAfterKeygen Concrete.scheme adversary
                  keyResult.1.1 keyResult.1.2)).run keyResult.2] +
            (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
      apply ENNReal.tsum_le_tsum
      intro keyResult
      by_cases hkeygen : keyResult ∈ support
          ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅)
      · apply mul_le_mul_right
        have hkeySupport : keyResult.1 ∈ support Concrete.scheme.keygen := by
          apply support_simulateQ_run'_subset xmssRomImpl Concrete.scheme.keygen ∅
          rw [StateT.run'_eq, support_map]
          exact ⟨keyResult, hkeygen, rfl⟩
        have hcontinuationBound :
            (detailedGameAfterKeygen Concrete.scheme adversary
              keyResult.1.1 keyResult.1.2).IsQueryBoundP (· matches .inr _) q :=
          OracleComp.IsQueryBoundP.continuation_mono_of_mem_support
            (· matches .inr _) Concrete.scheme.keygen
            (fun key => detailedGameAfterKeygen Concrete.scheme adversary key.1 key.2)
            q hdetailedBound keyResult.1 hkeySupport
        let continuation :=
          (simulateQ xmssRomImpl
            (detailedGameAfterKeygen Concrete.scheme adversary
              keyResult.1.1 keyResult.1.2)).run keyResult.2
        let collision := fun execution : GameOutcome × QueryCache HashSpec =>
          Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
            (keygenChainTargetInput keyResult.1.2 keyResult.2)
        calc
          Pr[fun execution : GameOutcome × QueryCache HashSpec =>
              OutcomeBadEventOccurs execution.2 execution.1 (.chain chain) |
              continuation] ≤
            Pr[fun execution : GameOutcome × QueryCache HashSpec =>
              OutcomeChainValueRevealed execution.2 execution.1 chain ∨
                collision execution | continuation] := by
              apply probEvent_mono
              intro execution hexecution hevent
              exact chain_event_afterKeygen_revealed_or_collision adversary keyResult
                hkeygen execution hexecution chain hevent
          _ ≤ Pr[fun execution : GameOutcome × QueryCache HashSpec =>
                OutcomeChainValueRevealed execution.2 execution.1 chain |
                continuation] + Pr[collision | continuation] :=
            probEvent_or_le continuation _ _
          _ ≤ Pr[fun execution : GameOutcome × QueryCache HashSpec =>
                OutcomeChainValueRevealed execution.2 execution.1 chain |
                continuation] +
              (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
            gcongr
            exact Rom.mixed_adaptiveFreshDigestCollisionWith_le
              (detailedGameAfterKeygen Concrete.scheme adversary
                keyResult.1.1 keyResult.1.2) q hcontinuationBound keyResult.2
              (keygenChainTargetInput keyResult.1.2 keyResult.2) collision
              (fun _ _ hcollision => hcollision)
      · rw [probOutput_eq_zero_of_not_mem_support hkeygen]
        simp only [zero_mul]
        exact le_rfl
    _ = ∑' keyResult, (
        Pr[= keyResult | (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅] *
            Pr[fun execution : GameOutcome × QueryCache HashSpec =>
              OutcomeChainValueRevealed execution.2 execution.1 chain |
              (simulateQ xmssRomImpl
                (detailedGameAfterKeygen Concrete.scheme adversary
                  keyResult.1.1 keyResult.1.2)).run keyResult.2] +
          Pr[= keyResult | (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅] *
            ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal))) := by
      apply tsum_congr
      intro keyResult
      rw [left_distrib]
    _ =
      (∑' keyResult,
        Pr[= keyResult | (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅] *
          Pr[fun execution : GameOutcome × QueryCache HashSpec =>
            OutcomeChainValueRevealed execution.2 execution.1 chain |
            (simulateQ xmssRomImpl
              (detailedGameAfterKeygen Concrete.scheme adversary
                keyResult.1.1 keyResult.1.2)).run keyResult.2]) +
        (∑' keyResult,
          Pr[= keyResult | (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅]) *
          ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤
      (∑' keyResult,
        Pr[= keyResult | (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅] *
          Pr[fun execution : GameOutcome × QueryCache HashSpec =>
            OutcomeChainValueRevealed execution.2 execution.1 chain |
            (simulateQ xmssRomImpl
              (detailedGameAfterKeygen Concrete.scheme adversary
                keyResult.1.1 keyResult.1.2)).run keyResult.2]) +
        (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
      apply add_le_add_right
      calc
        (∑' keyResult,
            Pr[= keyResult | (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅]) *
            ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) ≤
          1 * ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) :=
            mul_le_mul_left tsum_probOutput_le_one _
        _ = (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := one_mul _

end XmssSecurity

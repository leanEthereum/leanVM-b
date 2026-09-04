import SphincsSecurity.Proof.Amortized
import SphincsSecurity.Proof.Charge
import SphincsSecurity.Proof.Guess
import SphincsSecurity.Proof.Secrets

/-!
# The amortized step for the cache-local bad event

The finite target set for a fresh query, assembled from the four cache cases proven in `Charge`.
`Step` packages the witness in an inductive proposition so Lean does not repeatedly unfold the
enormous finite sum in `potential` while elaborating the dispatcher.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

attribute [local irreducible] potential

set_option maxHeartbeats 1000

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

private theorem growth_empty (n : Nat) :
    (n + 1 + numChains) + (∅ : Finset Digest).card ≤ n + 44 := by
  norm_num [numChains]

private theorem empty_growth (n : Nat) : n + (∅ : Finset Digest).card ≤ n + 44 := by
  norm_num

private theorem singleton_card_le (n : Nat) (target : Digest) :
    ({target} : Finset Digest).card ≤ n + 44 := by
  simp only [Finset.card_singleton]
  omega

private theorem singleton_growth (n : Nat) (target : Digest) :
    n + ({target} : Finset Digest).card ≤ n + 44 := by
  simp only [Finset.card_singleton]
  omega

/-- The target set and both obligations needed by `Amortized.probEvent_bad_le_amortized`. -/
inductive Step (cache : QueryCache HashSpec) (input₀ : HashInput) : Prop where
  | intro (targets : Finset Digest)
      (card_le : targets.card ≤ potential parameter otsSecret ftsSecret cache + 44)
      (safe : ∀ answer : HashOutput, truncateHash answer ∉ targets →
        ¬ Bad parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer)
          ∧ potential parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) + targets.card
            ≤ potential parameter otsSecret ftsSecret cache + 44) : Step cache input₀

private theorem step_of_unsettled_after {cache : QueryCache HashSpec} {input₀ : HashInput}
    {p₀ : Position} (hclean : ¬ Bad parameter otsSecret ftsSecret cache)
    (huncached : cache input₀ = none) (hposition : AtPosition parameter input₀ p₀)
    (hunsettled : ∀ answer : HashOutput,
      ¬ Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p₀) :
    Step parameter otsSecret ftsSecret cache input₀ := by
  refine Step.intro (parameter := parameter) (otsSecret := otsSecret) (ftsSecret := ftsSecret)
    (cache := cache) (input₀ := input₀) ∅ (Nat.zero_le _) (fun answer _ => ?_)
  have hunsettled' := hunsettled answer
  refine ⟨clean_cacheQuery_of_unsettled parameter otsSecret ftsSecret hclean
      (cache := cache) (input₀ := input₀) (answer := answer) (p₀ := p₀)
      huncached hposition hunsettled', ?_⟩
  have hpotential := potential_cacheQuery_le_of_unsettled parameter otsSecret ftsSecret
    (cache := cache) (input₀ := input₀) (answer := answer) (p₀ := p₀)
    huncached hposition hunsettled'
  exact (Nat.add_le_add hpotential (Nat.le_refl _)).trans
    (growth_empty (potential parameter otsSecret ftsSecret cache))

private theorem step_of_settling {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {input₀ : HashInput} {p₀ : Position}
    (hclean : ¬ Bad parameter otsSecret ftsSecret cache) (huncached : cache input₀ = none)
    (hposition : AtPosition parameter input₀ p₀)
    (hsettled : ¬ Settled parameter otsSecret ftsSecret cache p₀)
    (hsettles : ∀ answer : HashOutput,
      Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p₀) :
    Step parameter otsSecret ftsSecret cache input₀ := by
  have hpaid := potential_add_settlingTargets_card_le parameter otsSecret ftsSecret
    (cache := cache) hfinite (input₀ := input₀) (answer := 0) (p₀ := p₀)
    huncached hposition hsettled (hsettles 0)
  have hcardBase : (settlingTargets parameter cache hfinite p₀).card
      ≤ potential parameter otsSecret ftsSecret cache :=
    (Nat.le_add_left (settlingTargets parameter cache hfinite p₀).card
      (potential parameter otsSecret ftsSecret (cache.cacheQuery input₀ 0))).trans hpaid
  have hcard := hcardBase.trans
    (Nat.le_add_right (potential parameter otsSecret ftsSecret cache) 44)
  refine Step.intro (parameter := parameter) (otsSecret := otsSecret) (ftsSecret := ftsSecret)
    (cache := cache) (input₀ := input₀) (settlingTargets parameter cache hfinite p₀) hcard
    (fun answer hanswer => ?_)
  have hsettled' := hsettles answer
  refine ⟨clean_cacheQuery_of_settling_of_avoids parameter otsSecret ftsSecret
    hfinite hclean huncached hposition hsettled hsettled' hanswer, ?_⟩
  exact (potential_add_settlingTargets_card_le parameter otsSecret ftsSecret
    (cache := cache) hfinite (input₀ := input₀) (answer := answer) (p₀ := p₀)
    huncached hposition hsettled hsettled').trans
      (Nat.le_add_right (potential parameter otsSecret ftsSecret cache) 44)

private theorem step_at_unsettled {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {input₀ : HashInput} {p₀ : Position}
    (hclean : ¬ Bad parameter otsSecret ftsSecret cache) (huncached : cache input₀ = none)
    (hposition : AtPosition parameter input₀ p₀)
    (hsettled : ¬ Settled parameter otsSecret ftsSecret cache p₀) :
    Step parameter otsSecret ftsSecret cache input₀ := by
  by_cases hinput : input₀ = cachedInput parameter otsSecret ftsSecret cache p₀
  · by_cases hvalid : p₀.Valid
    · by_cases hchildren : ∀ c ∈ p₀.children, Settled parameter otsSecret ftsSecret cache c
      · apply step_of_settling parameter otsSecret ftsSecret hfinite hclean huncached
          hposition hsettled
        intro answer
        have hle := le_cacheQuery (cache := cache) (input := input₀) (answer := answer) huncached
        have hchildren' : ∀ c ∈ p₀.children,
            Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) c :=
          fun c hc => (hchildren c hc).mono hle
        have hvalues : ∀ c ∈ p₀.children,
            honestValue (fromCache (cache.cacheQuery input₀ answer)) parameter otsSecret ftsSecret c
              = honestValue (fromCache cache) parameter otsSecret ftsSecret c := fun c hc =>
          honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hle) (hchildren c hc)
        have hpinned : cachedInput parameter otsSecret ftsSecret
              (cache.cacheQuery input₀ answer) p₀
            = cachedInput parameter otsSecret ftsSecret cache p₀ :=
          honestInput_congr _ _ parameter otsSecret ftsSecret hvalid hvalues
        rw [settled_iff]
        refine ⟨hvalid, ?_, hchildren'⟩
        rw [hpinned, ← hinput, QueryCache.cacheQuery_self]
        simp
      · apply step_of_unsettled_after parameter otsSecret ftsSecret hclean huncached hposition
        intro answer hsettled'
        exact hchildren (eq_cachedInput_and_children_of_settled_cacheQuery
          parameter otsSecret ftsSecret huncached hposition hsettled hsettled').2
    · apply step_of_unsettled_after parameter otsSecret ftsSecret hclean huncached hposition
      exact fun _ hs => hvalid hs.valid
  · apply step_of_unsettled_after parameter otsSecret ftsSecret hclean huncached hposition
    intro answer hsettled'
    exact hinput (eq_cachedInput_and_children_of_settled_cacheQuery
      parameter otsSecret ftsSecret huncached hposition hsettled hsettled').1

private theorem step_at_position {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {input₀ : HashInput} {p₀ : Position}
    (hclean : ¬ Bad parameter otsSecret ftsSecret cache) (huncached : cache input₀ = none)
    (hposition : AtPosition parameter input₀ p₀) :
    Step parameter otsSecret ftsSecret cache input₀ := by
  by_cases hsettled : Settled parameter otsSecret ftsSecret cache p₀
  · let target := honestValue (fromCache cache) parameter otsSecret ftsSecret p₀
    refine Step.intro (parameter := parameter) (otsSecret := otsSecret) (ftsSecret := ftsSecret)
      (cache := cache) (input₀ := input₀) {target}
      (singleton_card_le (potential parameter otsSecret ftsSecret cache) target)
      (fun answer hanswer => ?_)
    have havoid : truncateHash answer ≠ target := by simpa [target] using hanswer
    refine ⟨clean_cacheQuery_of_settled_of_avoids parameter otsSecret ftsSecret hclean
      huncached hposition hsettled havoid, ?_⟩
    have hpotential := potential_cacheQuery_le_of_settled parameter otsSecret ftsSecret
      (cache := cache) (input₀ := input₀) (answer := answer) (p₀ := p₀)
      huncached hposition hsettled
    exact (Nat.add_le_add hpotential (Nat.le_refl _)).trans
      (singleton_growth (potential parameter otsSecret ftsSecret cache) target)
  · exact step_at_unsettled parameter otsSecret ftsSecret hfinite hclean huncached
      hposition hsettled

/-- **The per-query charge.** A fresh answer is dangerous only inside targets paid for by the
current potential and `44` new units. -/
theorem bad_step (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (hclean : ¬ Bad parameter otsSecret ftsSecret cache) (input₀ : HashInput)
    (huncached : cache input₀ = none) : Step parameter otsSecret ftsSecret cache input₀ := by
  classical
  by_cases hAt : ∃ p, AtPosition parameter input₀ p
  · obtain ⟨p₀, hposition⟩ := hAt
    exact step_at_position parameter otsSecret ftsSecret hfinite hclean huncached hposition
  · refine Step.intro (parameter := parameter) (otsSecret := otsSecret) (ftsSecret := ftsSecret)
      (cache := cache) (input₀ := input₀) ∅ (Nat.zero_le _) (fun answer _ => ?_)
    obtain ⟨hclean', hpotential⟩ := clean_and_potential_cacheQuery_of_not_atPosition
      parameter otsSecret ftsSecret hclean huncached (fun p hp => hAt ⟨p, hp⟩)
    refine ⟨hclean', ?_⟩
    exact (Nat.add_le_add hpotential (Nat.le_refl _)).trans
      (empty_growth (potential parameter otsSecret ftsSecret cache))

/-- **The amortized bad-event bound.** A `q`-query computation makes `Bad` true with probability at
most `(44q + potential) / 2^128`. -/
theorem probEvent_bad_le {α : Type} (oa : OracleComp OracleWorld α) (q : Nat)
    (hq : oa.IsQueryBoundP (· matches Sum.inr _) q) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hclean : ¬ Bad parameter otsSecret ftsSecret cache) :
    Pr[fun result => Bad parameter otsSecret ftsSecret result.2
        | (simulateQ romImpl oa).run cache]
      ≤ ((44 * q + potential parameter otsSecret ftsSecret cache : Nat) : ℝ≥0∞)
          * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply probEvent_bad_le_amortized
    (Bad := Bad parameter otsSecret ftsSecret) (Inv := Finite)
    (potential := potential parameter otsSecret ftsSecret) (c := 44)
  · intro target
    rw [← probOutput_map]
    exact probOutput_truncateHash_le target
  · intro cache' input answer hfinite'
    exact finite_cacheQuery hfinite' input answer
  · intro cache' hfinite' hclean' input huncached
    rcases bad_step parameter otsSecret ftsSecret cache' hfinite' hclean' input huncached with
      ⟨targets, hcard, hsafe⟩
    exact ⟨targets, hcard, hsafe⟩
  · exact hq
  · exact hfinite
  · exact hclean

namespace Concrete

/-- The accounted SPHINCS run starts clean with zero potential, so its structural-hit probability is
at most `44q / 2^128`. -/
theorem probEvent_bad_gameAfterSecrets_le (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hq : (gameAfterSecrets adversary parameter otsSecret ftsSecret).IsQueryBoundP
      (· matches Sum.inr _) q) :
    Pr[fun result => Bad parameter otsSecret ftsSecret result.2
        | (simulateQ romImpl (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅]
      ≤ ((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  have hbound := probEvent_bad_le parameter otsSecret ftsSecret
    (gameAfterSecrets adversary parameter otsSecret ftsSecret) q hq ∅
    finite_empty (not_bad_empty parameter otsSecret ftsSecret)
  rw [potential_empty, Nat.add_zero] at hbound
  exact hbound

end Concrete

set_option maxHeartbeats 0

end SphincsSecurity

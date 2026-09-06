import SphincsSecurity.Proof.AnswerCharge
import SphincsSecurity.Proof.TightEncodingChildrenCharge

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

attribute [local irreducible] instFintypePosition answerPotential

private theorem answer_growth_empty (n : Nat) :
    (n + 1) + (∅ : Finset Digest).card ≤ n + 1 := by
  simp

private theorem answer_empty_growth (n : Nat) : n + (∅ : Finset Digest).card ≤ n + 1 := by
  simp

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

theorem clean_cacheQuery_of_settling_without_parent {cache : QueryCache HashSpec}
    (hfinite : Finite cache) {input₀ : HashInput} {answer : HashOutput} {p₀ : Position}
    (hclean : ¬ Bad parameter otsSecret ftsSecret cache) (huncached : cache input₀ = none)
    (hposition : AtPosition parameter input₀ p₀)
    (hunsettled : ¬ Settled parameter otsSecret ftsSecret cache p₀)
    (hsettled : Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p₀)
    (hnoParent : ¬ ParentSettlement parameter otsSecret ftsSecret cache input₀ answer)
    (havoid : truncateHash answer ∉ answerTargets parameter cache hfinite p₀) :
    ¬ Bad parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) := by
  have hle : cache ≤ cache.cacheQuery input₀ answer := le_cacheQuery huncached
  obtain ⟨hinput₀, hchildren⟩ := eq_cachedInput_and_children_of_settled_cacheQuery
    parameter otsSecret ftsSecret huncached hposition hunsettled hsettled
  have hvalues : ∀ c ∈ p₀.children,
      honestValue (fromCache (cache.cacheQuery input₀ answer)) parameter otsSecret ftsSecret c
        = honestValue (fromCache cache) parameter otsSecret ftsSecret c := fun c hc =>
    honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hle) (hchildren c hc)
  have hpinned₀ : cachedInput parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p₀
      = cachedInput parameter otsSecret ftsSecret cache p₀ :=
    honestInput_congr _ _ parameter otsSecret ftsSecret hsettled.valid hvalues
  have hinputNew : cachedInput parameter otsSecret ftsSecret
      (cache.cacheQuery input₀ answer) p₀ = input₀ := hpinned₀.trans hinput₀.symm
  have hparentClean : ∀ q parent, some p₀ = some q → q.parentOf = some parent →
      ¬ Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) parent := by
    intro q parent hq hparent
    rw [Option.some.injEq] at hq
    subst hq
    exact fun hs => hnoParent ⟨huncached, p₀, parent, hposition, hunsettled, hsettled, hparent, hs⟩
  rintro ⟨p, hsettled', input, ax, ay, hat, hne, hinput, hhonest, heq⟩
  by_cases hp : p = p₀
  · subst hp
    have hinputne : input ≠ input₀ := by rwa [hinputNew] at hne
    have hinputOld : cache input = some ax := by
      rwa [QueryCache.cacheQuery_of_ne _ _ hinputne] at hinput
    have hcachedAt : input ∈ cachedAt parameter cache p :=
      ⟨by simp [hinputOld], hat⟩
    have htarget : truncateHash ax ∈ answerTargets parameter cache hfinite p := by
      simpa [hinputOld] using mem_answerTargets parameter hfinite hcachedAt
    rw [hinputNew, QueryCache.cacheQuery_self] at hhonest
    have hanswer : answer = ay := Option.some.inj hhonest
    apply havoid
    have heqAnswer : truncateHash answer = truncateHash ax := by rw [hanswer, ← heq]
    rw [heqAnswer]
    exact htarget
  · have hsettledOld : Settled parameter otsSecret ftsSecret cache p :=
      settled_of_settled_cacheQuery parameter otsSecret ftsSecret huncached
        (p₀ := some p₀) (fun q hq => by
          rw [atPosition_unique parameter hposition hq]) hparentClean
        (p.depth + 1) p (by omega) (by
          intro heq
          exact hp (Option.some.inj heq).symm) hsettled'
    have hpinned := cachedInput_eq_of_settled hle hsettledOld
    have hinputne : input ≠ input₀ := atPosition_ne parameter hat hposition hp
    have hhonestne : cachedInput parameter otsSecret ftsSecret cache p ≠ input₀ :=
      atPosition_ne parameter (atPosition_cachedInput parameter otsSecret ftsSecret cache p)
        hposition hp
    have hinputOld : cache input = some ax := by
      rwa [QueryCache.cacheQuery_of_ne _ _ hinputne] at hinput
    rw [hpinned, QueryCache.cacheQuery_of_ne _ _ hhonestne] at hhonest
    apply hclean
    refine ⟨p, hsettledOld, input, ax, ay, hat, ?_, hinputOld, hhonest, heq⟩
    rwa [hpinned] at hne

inductive AnswerStep (cache : QueryCache HashSpec) (input : HashInput) : Prop where
  | intro (targets : Finset Digest)
      (card_le : targets.card ≤ answerPotential parameter otsSecret ftsSecret cache + 1)
      (safe : ∀ answer : HashOutput, ¬ ParentSettlement parameter otsSecret ftsSecret cache input answer →
        truncateHash answer ∉ targets →
          ¬ Bad parameter otsSecret ftsSecret (cache.cacheQuery input answer) ∧
            answerPotential parameter otsSecret ftsSecret (cache.cacheQuery input answer) + targets.card ≤
              answerPotential parameter otsSecret ftsSecret cache + 1) : AnswerStep cache input

theorem answerStep_of_settled {cache : QueryCache HashSpec} {input : HashInput} {position : Position}
    (hclean : ¬ Bad parameter otsSecret ftsSecret cache) (hfresh : cache input = none)
    (hat : AtPosition parameter input position) (hs : Settled parameter otsSecret ftsSecret cache position) :
    AnswerStep parameter otsSecret ftsSecret cache input := by
  refine AnswerStep.intro {honestValue (fromCache cache) parameter otsSecret ftsSecret position} (by simp) ?_
  intro answer _ havoid
  refine ⟨clean_cacheQuery_of_settled_of_avoids parameter otsSecret ftsSecret hclean hfresh hat hs
    (by simpa only [Finset.mem_singleton] using havoid), ?_⟩
  simpa only [Finset.card_singleton] using Nat.add_le_add_right
    (answerPotential_cacheQuery_le_of_settled parameter otsSecret ftsSecret (answer := answer) hfresh hat hs) 1

theorem answerStep_of_unsettled_after {cache : QueryCache HashSpec} {input : HashInput} {position : Position}
    (hclean : ¬ Bad parameter otsSecret ftsSecret cache) (hfresh : cache input = none)
    (hat : AtPosition parameter input position)
    (hnever : ∀ answer : HashOutput, ¬ Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) position) :
    AnswerStep parameter otsSecret ftsSecret cache input := by
  refine AnswerStep.intro ∅ (Nat.zero_le _) ?_
  intro answer _ _
  refine ⟨clean_cacheQuery_of_unsettled parameter otsSecret ftsSecret hclean hfresh hat (hnever answer), ?_⟩
  exact (Nat.add_le_add
    (answerPotential_cacheQuery_le_one parameter otsSecret ftsSecret (answer := answer) hfresh hat)
    (Nat.le_refl _)).trans (answer_growth_empty (answerPotential parameter otsSecret ftsSecret cache))

theorem answerStep_of_settling {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {input : HashInput} {position : Position} {settlingAnswer : HashOutput}
    (hclean : ¬ Bad parameter otsSecret ftsSecret cache) (hfresh : cache input = none)
    (hat : AtPosition parameter input position) (hs : ¬ Settled parameter otsSecret ftsSecret cache position)
    (hsettles : Settled parameter otsSecret ftsSecret (cache.cacheQuery input settlingAnswer) position) :
    AnswerStep parameter otsSecret ftsSecret cache input := by
  have hpaid := answerPotential_add_answerTargets_card_le parameter otsSecret ftsSecret hfinite hfresh hat hs hsettles
  have hcard : (answerTargets parameter cache hfinite position).card ≤ answerPotential parameter otsSecret ftsSecret cache :=
    (Nat.le_add_left _ _).trans hpaid
  refine AnswerStep.intro (answerTargets parameter cache hfinite position) (hcard.trans (Nat.le_add_right _ 1)) ?_
  intro answer hnoParent havoid
  have hafter := settled_cacheQuery_of_settled_cacheQuery parameter otsSecret ftsSecret hfresh hat hs hsettles answer
  refine ⟨clean_cacheQuery_of_settling_without_parent parameter otsSecret ftsSecret hfinite
    hclean hfresh hat hs hafter hnoParent havoid, ?_⟩
  exact (answerPotential_add_answerTargets_card_le parameter otsSecret ftsSecret hfinite hfresh hat hs hafter).trans
    (Nat.le_add_right _ 1)

theorem answerStep_of_not_atPosition {cache : QueryCache HashSpec} {input : HashInput}
    (hclean : ¬ Bad parameter otsSecret ftsSecret cache) (hfresh : cache input = none)
    (hnot : ∀ position, ¬ AtPosition parameter input position) :
    AnswerStep parameter otsSecret ftsSecret cache input := by
  refine AnswerStep.intro ∅ (Nat.zero_le _) ?_
  intro answer _ _
  refine ⟨(clean_and_potential_cacheQuery_of_not_atPosition parameter otsSecret ftsSecret hclean hfresh hnot).1, ?_⟩
  exact (Nat.add_le_add
    (answerPotential_cacheQuery_le_of_not_atPosition parameter otsSecret ftsSecret (answer := answer) hfresh hnot)
    (Nat.le_refl _)).trans (answer_empty_growth (answerPotential parameter otsSecret ftsSecret cache))

theorem answerCharge_step {cache : QueryCache HashSpec} (hfinite : Finite cache)
    (hclean : ¬ Bad parameter otsSecret ftsSecret cache) (input : HashInput)
    (hfresh : cache input = none) :
    ∃ targets : Finset Digest, targets.card ≤ answerPotential parameter otsSecret ftsSecret cache + 1 ∧
      ∀ answer : HashOutput, ¬ ParentSettlement parameter otsSecret ftsSecret cache input answer →
        truncateHash answer ∉ targets →
          ¬ Bad parameter otsSecret ftsSecret (cache.cacheQuery input answer) ∧
            answerPotential parameter otsSecret ftsSecret (cache.cacheQuery input answer) + targets.card ≤
              answerPotential parameter otsSecret ftsSecret cache + 1 := by
  classical
  have hstep : AnswerStep parameter otsSecret ftsSecret cache input := by
    by_cases hposition : ∃ position, AtPosition parameter input position
    · obtain ⟨position, hat⟩ := hposition
      by_cases hs : Settled parameter otsSecret ftsSecret cache position
      · exact answerStep_of_settled parameter otsSecret ftsSecret hclean hfresh hat hs
      · by_cases hnever : ∀ answer : HashOutput,
            ¬ Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) position
        · exact answerStep_of_unsettled_after parameter otsSecret ftsSecret hclean hfresh hat hnever
        · push Not at hnever
          obtain ⟨answer, hafter⟩ := hnever
          exact answerStep_of_settling parameter otsSecret ftsSecret hfinite hclean hfresh hat hs hafter
    · exact answerStep_of_not_atPosition parameter otsSecret ftsSecret hclean hfresh
        (fun position hat => hposition ⟨position, hat⟩)
  obtain ⟨targets, hcard, hsafe⟩ := hstep
  exact ⟨targets, hcard, hsafe⟩

end SphincsSecurity

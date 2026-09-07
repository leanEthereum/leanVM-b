import SphincsSecurity.Proof.HonestStructuralQueries
import SphincsSecurity.Proof.HashQueryCut
import SphincsSecurity.Proof.AnswerEncodingQueryBudget

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition

theorem queriedInputs_getElem_of_eval_hashQueryCutAt
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α) (ordinal : Nat)
    (input : HashInput) (next : HashOutput → OracleComp HashSpec α)
    (hcut : evalWithAnswerFn f (hashQueryCutAt computation ordinal) = .query input next) :
    (queriedInputs f computation)[ordinal]? = some input := by
  induction computation using OracleComp.inductionOn generalizing ordinal with
  | pure value => simp [hashQueryCutAt] at hcut
  | query_bind queried continuation ih =>
      cases ordinal with
      | zero =>
          have heq : queried = input := by
            simpa only [hashQueryCutAt, construct_query_bind, evalWithAnswerFn_pure, HashQueryCut.query.injEq] using
              congrArg (fun cut => match cut with | .done _ => queried | .query input _ => input) hcut
          simp only [queriedInputs_query_bind, List.getElem?_cons_zero, heq]
      | succ ordinal =>
          simp only [hashQueryCutAt, construct_query_bind, evalWithAnswerFn_bind] at hcut
          exact ih (f queried) ordinal hcut

theorem settled_at_supported_honest_query
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp HashSpec α)
    (hsettling : ∀ f, SettlingRun parameter otsSecret ftsSecret f computation)
    (hhonest : ∀ f, HonestStructuralQueries parameter otsSecret ftsSecret f computation)
    (ordinal : Nat) (initialCache cache : QueryCache HashSpec)
    (input : HashInput) (next : HashOutput → OracleComp HashSpec α)
    (hcut : (.query input next, cache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) (hashQueryCutAt computation ordinal)).run initialCache))
    (hfresh : cache input = none) :
    ∃ position : Position, AtPosition parameter input position ∧
      ¬ Settled parameter otsSecret ftsSecret cache position ∧
      ∀ answer : HashOutput, Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) position := by
  let f := fromCache cache
  have hprefix := replay_of_mem_support _ _ _ _ hcut f (agreesWithFn_fromCache cache)
  have hget := queriedInputs_getElem_of_eval_hashQueryCutAt f computation ordinal input next hprefix.2.1
  obtain ⟨position, hvalid, hinput⟩ := hhonest f input (List.mem_of_getElem? hget)
  have hat : AtPosition parameter input position := ⟨_, hinput⟩
  refine ⟨position, hat, ?_, ?_⟩
  · intro hsettled
    have heq := hinput.trans (honestInput_eq_cachedInput (agreesWithFn_fromCache cache) hsettled)
    exact hsettled.cached (heq ▸ hfresh)
  · intro answer
    let afterCache := cache.cacheQuery input answer
    let g := fromCache afterCache
    have hle : cache ≤ afterCache := le_cacheQuery hfresh
    have hprefix' := replay_of_mem_support _ _ _ _ hcut g (agreesWithFn_fromCache_of_le hle)
    have hget' := queriedInputs_getElem_of_eval_hashQueryCutAt g computation ordinal input next hprefix'.2.1
    apply hsettling g ordinal input hget' afterCache (agreesWithFn_fromCache afterCache) _ position hat
    intro prior hprior
    rw [List.take_add_one, hget', Option.toList_some, List.mem_append, List.mem_singleton] at hprior
    rcases hprior with hprior | rfl
    · obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp
        (hprefix'.2.2 prior (by rwa [queriedInputs_hashQueryCutAt]))
      rw [hle hvalue]
      exact Option.some_ne_none _
    · dsimp only [afterCache]
      rw [QueryCache.cacheQuery_self]
      exact Option.some_ne_none _

namespace Concrete

theorem ftsParentQueryCharge_eq_zero_of_children_settled
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (position : Position) (hat : AtPosition secretKey.parameter input position)
    (hchildren : ∀ child ∈ position.children, Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache child) :
    ftsParentQueryCharge secretKey cache input = 0 := by
  have hnotParent : ¬ ∃ candidate : Position, AtPosition secretKey.parameter input candidate ∧ ¬ OtsProbeSimulation.IsOtsPosition candidate ∧
      ¬ ∀ child ∈ candidate.children, Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache child := by
    rintro ⟨candidate, hc, _, hn⟩
    exact hn (atPosition_unique secretKey.parameter hat hc ▸ hchildren)
  simp only [ftsParentQueryCharge, parentReserveCharge, if_neg hnotParent, Nat.cast_zero]

theorem parentStoppedEncoding_add_ftsParent_eq_zero_of_settling
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput)
    (position : Position) (hat : AtPosition secretKey.parameter input position)
    (hfresh : cache input = none)
    (hbefore : ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position)
    (hafter : ∀ answer : HashOutput, Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret (cache.cacheQuery input answer) position) :
    parentStoppedEncodingQueryCharge secretKey cache input + ftsParentQueryCharge secretKey cache input = 0 := by
  have hnotEncoding : ¬ ∃ encoding : EncodingPosition, AtEncodingPosition secretKey.parameter input encoding := by
    rintro ⟨encoding, he⟩
    exact he.not_atPosition position hat
  have hchildren := (eq_cachedInput_and_children_of_settled_cacheQuery secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
    hfresh hat hbefore (hafter 0)).2
  rw [ftsParentQueryCharge_eq_zero_of_children_settled secretKey cache input position hat hchildren, add_zero]
  simp only [parentStoppedEncodingQueryCharge, if_pos hfresh, dif_neg hnotEncoding,
    if_pos (show ∃ candidate : Position, AtPosition secretKey.parameter input candidate ∧
      ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache candidate ∧
      ∀ answer : HashOutput, Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret (cache.cacheQuery input answer) candidate
      from ⟨position, hat, hbefore, hafter⟩)]

theorem structuralCharge_eq_zero_at_supported_honest_query
    (secretKey : SecretKey) (computation : OracleComp HashSpec α)
    (hsettling : ∀ f, SettlingRun secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f computation)
    (hhonest : ∀ f, HonestStructuralQueries secretKey.parameter secretKey.otsSecret secretKey.ftsSecret f computation)
    (ordinal : Nat) (initialCache cache : QueryCache HashSpec)
    (input : HashInput) (next : HashOutput → OracleComp HashSpec α)
    (hcut : (.query input next, cache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) (hashQueryCutAt computation ordinal)).run initialCache)) :
    parentStoppedEncodingQueryCharge secretKey cache input + ftsParentQueryCharge secretKey cache input = 0 := by
  by_cases hfresh : cache input = none
  · obtain ⟨position, hat, hbefore, hafter⟩ := settled_at_supported_honest_query
      secretKey.parameter secretKey.otsSecret secretKey.ftsSecret computation hsettling hhonest ordinal initialCache cache input next hcut hfresh
    exact parentStoppedEncoding_add_ftsParent_eq_zero_of_settling secretKey cache input position hat hfresh hbefore hafter
  · let f := fromCache cache
    have hprefix := replay_of_mem_support _ _ _ _ hcut f (agreesWithFn_fromCache cache)
    have hget := queriedInputs_getElem_of_eval_hashQueryCutAt f computation ordinal input next hprefix.2.1
    obtain ⟨position, _, hinput⟩ := hhonest f input (List.mem_of_getElem? hget)
    have hat : AtPosition secretKey.parameter input position := ⟨_, hinput⟩
    have hs : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position := by
      apply hsettling f ordinal input hget cache (agreesWithFn_fromCache cache) _ position hat
      intro prior hprior
      rw [List.take_add_one, hget, Option.toList_some, List.mem_append, List.mem_singleton] at hprior
      rcases hprior with hprior | rfl
      · exact hprefix.2.2 prior (by rwa [queriedInputs_hashQueryCutAt])
      · exact hfresh
    rw [ftsParentQueryCharge_eq_zero_of_children_settled secretKey cache input position hat hs.children,
      parentStoppedEncodingQueryCharge, if_neg hfresh, add_zero]

end Concrete
end SphincsSecurity

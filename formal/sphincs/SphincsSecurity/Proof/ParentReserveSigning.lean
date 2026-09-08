import SphincsSecurity.Proof.ParentReserveConservation
import SphincsSecurity.Proof.SigningParentSettlement

namespace SphincsSecurity

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem parentReserve_le_of_new_inputs_settled
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (eligible : Position → Prop)
    (before after : QueryCache HashSpec) (hle : before ≤ after)
    (hnew : ∀ input position, AtPosition parameter input position → before input = none → after input ≠ none →
      Settled parameter otsSecret ftsSecret after position) :
    parentReserve parameter otsSecret ftsSecret eligible after ≤ parentReserve parameter otsSecret ftsSecret eligible before := by
  apply Finset.sum_le_sum
  intro position _
  by_cases hchildren : ∀ child ∈ position.children, Settled parameter otsSecret ftsSecret after child
  · rw [parentReserveContribution, if_neg (fun h => h.2 hchildren)]
    exact Nat.zero_le _
  · apply parentReserveContribution_le_of_cachedAt_eq parameter otsSecret ftsSecret eligible hle position
    apply Set.Subset.antisymm
    · intro input hi
      refine ⟨?_, hi.2⟩
      intro hn
      exact hchildren (hnew input position hi.2 hn hi.1).children
    · intro input hi
      obtain ⟨answer, ha⟩ := Option.ne_none_iff_exists'.mp hi.1
      exact ⟨by rw [hle ha]; exact Option.some_ne_none answer, hi.2⟩

theorem parentReserve_le_of_settlingRun
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (eligible : Position → Prop)
    (computation : OracleComp HashSpec α)
    (hsettling : ∀ f, SettlingRun parameter otsSecret ftsSecret f computation)
    (before after : QueryCache HashSpec) (value : α)
    (hr : (value, after) ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run before)) :
    parentReserve parameter otsSecret ftsSecret eligible after ≤ parentReserve parameter otsSecret ftsSecret eligible before := by
  let f := fromCache after
  have hf := agreesWithFn_fromCache after
  have hreplay := replay_of_mem_support _ _ _ _ hr f hf
  apply parentReserve_le_of_new_inputs_settled parameter otsSecret ftsSecret eligible before after hreplay.1
  intro input position hat hn hc
  have hqueried : input ∈ queriedInputs f computation := by
    by_contra hnot
    exact hc (cache_eq_none_of_not_mem_queriedInputs _ _ _ _ hr f hf input hn hnot)
  exact (hsettling f).settled_of_prefix (List.append_nil _).symm hf hreplay.2.2 hqueried hat

namespace Concrete

theorem parentReserve_signDigestLoop_le (key : SecretKey) (eligible : Position → Prop)
    (attempts : Nat) (message : Message) (before after : QueryCache HashSpec) (value)
    (hr : (value, after) ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run before)) :
    parentReserve key.parameter key.otsSecret key.ftsSecret eligible after ≤ parentReserve key.parameter key.otsSecret key.ftsSecret eligible before := by
  apply parentReserve_le_of_new_inputs_settled key.parameter key.otsSecret key.ftsSecret eligible before after
    (simulateQ_romImpl_cache_le _ _ _ hr)
  intro input position hat hn hc
  exact False.elim (hc (signDigestLoop_cache_structural_none attempts key message before after value hr input position hat hn))

theorem parentReserve_sign_le (key : SecretKey) (eligible : Position → Prop)
    (message : Message) (before after : QueryCache HashSpec) (value)
    (hr : (value, after) ∈ support ((simulateQ romImpl (sign key message)).run before)) :
    parentReserve key.parameter key.otsSecret key.ftsSecret eligible after ≤ parentReserve key.parameter key.otsSecret key.ftsSecret eligible before := by
  rw [sign_eq_digestLoop_afterDigest, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨⟨selected, middle⟩, hm, ht⟩ := hr
  have hmiddle := parentReserve_signDigestLoop_le key eligible digestAttemptLimit message before middle selected hm
  cases selected with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at ht
      exact ht.2 ▸ hmiddle
  | some selected =>
      rw [simulateQ_romImpl_liftM] at ht
      exact (parentReserve_le_of_settlingRun key.parameter key.otsSecret key.ftsSecret eligible
        (signAfterDigest key selected.1 selected.2.1 selected.2.2)
        (fun f => settlingRun_signAfterDigest f key selected.1 selected.2.1 selected.2.2) middle after value ht).trans hmiddle

end Concrete
end SphincsSecurity

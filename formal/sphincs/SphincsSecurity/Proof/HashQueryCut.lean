import SphincsSecurity.Proof.SettlingTrace
import SphincsSecurity.Proof.ParentSettlementWitness

namespace SphincsSecurity

open OracleComp OracleSpec

inductive HashQueryCut (α : Type) where
  | done (value : α)
  | query (input : HashInput) (next : HashOutput → OracleComp HashSpec α)

def HashQueryCut.resume : HashQueryCut α → OracleComp HashSpec α
  | .done value => pure value
  | .query input next => (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) >>= next

noncomputable def hashQueryCutAt (computation : OracleComp HashSpec α) : Nat → OracleComp HashSpec (HashQueryCut α) :=
  OracleComp.construct (fun value _ => pure (.done value))
    (fun input next recursivelyCut ordinal =>
      match ordinal with
      | 0 => pure (.query input next)
      | ordinal + 1 => OracleSpec.query input >>= fun output => recursivelyCut output ordinal) computation

theorem hashQueryCutAt_resume (computation : OracleComp HashSpec α) (ordinal : Nat) :
    hashQueryCutAt computation ordinal >>= HashQueryCut.resume = computation := by
  induction computation using OracleComp.inductionOn generalizing ordinal with
  | pure value => rfl
  | query_bind input next ih =>
      cases ordinal with
      | zero => rfl
      | succ ordinal =>
          change (((liftM (OracleSpec.query input) : OracleComp HashSpec _) >>=
            fun output => hashQueryCutAt (next output) ordinal) >>= HashQueryCut.resume) = _
          rw [bind_assoc]
          exact bind_congr fun output => ih output ordinal

theorem queriedInputs_hashQueryCutAt (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) (ordinal : Nat) :
    queriedInputs f (hashQueryCutAt computation ordinal) = (queriedInputs f computation).take ordinal := by
  induction computation using OracleComp.inductionOn generalizing ordinal with
  | pure value => simp [hashQueryCutAt]
  | query_bind input next ih =>
      cases ordinal with
      | zero => simp [hashQueryCutAt]
      | succ ordinal =>
          rw [hashQueryCutAt, OracleComp.construct_query_bind]
          simp only [queriedInputs_query_bind, List.take_succ_cons]
          congr 1
          exact ih (f input) ordinal

theorem mem_support_hashQueryCutAt_resume_iff
    (computation : OracleComp HashSpec α) (ordinal : Nat)
    (initialCache : QueryCache HashSpec) (result : α × QueryCache HashSpec) :
    result ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run initialCache) ↔
      ∃ cut : HashQueryCut α, ∃ middleCache : QueryCache HashSpec,
        (cut, middleCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec _) (hashQueryCutAt computation ordinal)).run initialCache) ∧
        result ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _) cut.resume).run middleCache) := by
  conv_lhs => rw [← hashQueryCutAt_resume computation ordinal]
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  constructor
  · rintro ⟨⟨cut, cache⟩, hcut, hrest⟩
    exact ⟨cut, cache, hcut, hrest⟩
  · rintro ⟨cut, cache, hcut, hrest⟩
    exact ⟨(cut, cache), hcut, hrest⟩

theorem SettlingRun.new_input_settled_at_cut
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest} {f : QueryImpl HashSpec Id}
    {computation : OracleComp HashSpec α}
    (hsettling : SettlingRun parameter otsSecret ftsSecret f computation)
    (ordinal : Nat) {initialCache middleCache : QueryCache HashSpec} {cut : HashQueryCut α}
    (hsupport : (cut, middleCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) (hashQueryCutAt computation ordinal)).run initialCache))
    (hf : middleCache.AgreesWithFn f) {input : HashInput}
    (hbefore : initialCache input = none) (hafter : middleCache input ≠ none)
    {position : Position} (hat : AtPosition parameter input position) :
    Settled parameter otsSecret ftsSecret middleCache position := by
  have hqueried : input ∈ queriedInputs f (hashQueryCutAt computation ordinal) := by
    by_contra hnot
    exact hafter (cache_eq_none_of_not_mem_queriedInputs _ _ _ _ hsupport f hf input hbefore hnot)
  have hcached := (replay_of_mem_support _ _ _ _ hsupport f hf).2.2
  rw [queriedInputs_hashQueryCutAt] at hqueried hcached
  exact hsettling.settled_of_prefix (List.take_append_drop ordinal _).symm hf hcached hqueried hat

theorem SettlingRun.parentSettlement_input_cached_initial
    {parameter : PublicParameter}
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest} {f : QueryImpl HashSpec Id}
    {computation : OracleComp HashSpec α}
    (hsettling : SettlingRun parameter otsSecret ftsSecret f computation)
    (ordinal : Nat) {initialCache middleCache finalCache : QueryCache HashSpec} {cut : HashQueryCut α}
    (hsupport : (cut, middleCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) (hashQueryCutAt computation ordinal)).run initialCache))
    (hf : middleCache.AgreesWithFn f) {input : HashInput} {answer : HashOutput}
    (hparent : ParentSettlement parameter otsSecret ftsSecret middleCache input answer)
    (hle : middleCache.cacheQuery input answer ≤ finalCache) :
    ∃ child parent,
      AtPosition parameter input child ∧ child.parentOf = some parent ∧
      ¬ Settled parameter otsSecret ftsSecret middleCache child ∧
      Settled parameter otsSecret ftsSecret finalCache parent ∧
      initialCache (cachedInput parameter otsSecret ftsSecret finalCache parent) ≠ none := by
  obtain ⟨child, parent, hat, hparentOf, hunsettled, _, _, hsettled, hcached, _⟩ :=
    hparent.exists_full_parent_input parameter otsSecret ftsSecret hle
  refine ⟨child, parent, hat, hparentOf, hunsettled, hsettled, ?_⟩
  intro hnone
  have hparentSettled := hsettling.new_input_settled_at_cut ordinal hsupport hf hnone hcached
    (atPosition_cachedInput parameter otsSecret ftsSecret finalCache parent)
  exact hunsettled (hparentSettled.children child (Position.mem_children_iff.mpr hparentOf))

end SphincsSecurity

import SphincsSecurity.Proof.Cached
import SphincsSecurity.Proof.Charge

namespace SphincsSecurity

open OracleComp OracleSpec

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (f : QueryImpl HashSpec Id)

def SettlingTrace (queries : List HashInput) : Prop :=
  ∀ (n : Nat) (input : HashInput), queries[n]? = some input →
    ∀ (cache : QueryCache HashSpec), cache.AgreesWithFn f →
      (∀ prior ∈ queries.take (n + 1), cache prior ≠ none) →
      ∀ position, AtPosition parameter input position → Settled parameter otsSecret ftsSecret cache position

def SettlingRun {α : Type} (computation : OracleComp HashSpec α) : Prop :=
  SettlingTrace parameter otsSecret ftsSecret f (queriedInputs f computation)

variable {parameter otsSecret ftsSecret f}

theorem SettlingTrace.nil : SettlingTrace parameter otsSecret ftsSecret f [] := by
  intro n input hinput
  simp at hinput

theorem SettlingTrace.append {left right : List HashInput}
    (hleft : SettlingTrace parameter otsSecret ftsSecret f left)
    (hright : SettlingTrace parameter otsSecret ftsSecret f right) :
    SettlingTrace parameter otsSecret ftsSecret f (left ++ right) := by
  intro n input hinput cache hf hcached position hat
  by_cases hn : n < left.length
  · rw [List.getElem?_append_left hn] at hinput
    apply hleft n input hinput cache hf _ position hat
    intro prior hprior
    apply hcached prior
    rwa [List.take_append_of_le_length (by omega)]
  · have hle : left.length ≤ n := by omega
    rw [List.getElem?_append_right hle] at hinput
    apply hright (n - left.length) input hinput cache hf _ position hat
    intro prior hprior
    apply hcached prior
    rw [List.take_append]
    apply List.mem_append_right
    simpa only [show n + 1 - left.length = n - left.length + 1 by omega] using hprior

theorem SettlingTrace.snoc {queries : List HashInput} {input : HashInput}
    (hqueries : SettlingTrace parameter otsSecret ftsSecret f queries)
    (hlast : ∀ (cache : QueryCache HashSpec), cache.AgreesWithFn f →
      (∀ prior ∈ queries ++ [input], cache prior ≠ none) →
      ∀ position, AtPosition parameter input position → Settled parameter otsSecret ftsSecret cache position) :
    SettlingTrace parameter otsSecret ftsSecret f (queries ++ [input]) := by
  intro n selected hselected cache hf hcached position hat
  by_cases hn : n < queries.length
  · rw [List.getElem?_append_left hn] at hselected
    apply hqueries n selected hselected cache hf _ position hat
    intro prior hprior
    apply hcached prior
    rwa [List.take_append_of_le_length (by omega)]
  · have hle : queries.length ≤ n := by omega
    rw [List.getElem?_append_right hle] at hselected
    have hn : n = queries.length := by
      have hlt := (List.getElem?_eq_some_iff.mp hselected).1
      simp only [List.length_singleton] at hlt
      omega
    subst n
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hselected
    subst selected
    apply hlast cache hf _ position hat
    simpa only [show queries.length + 1 = (queries ++ [input]).length by simp,
      List.take_length] using hcached

theorem SettlingTrace.of_no_position {queries : List HashInput}
    (h : ∀ input ∈ queries, ∀ position, ¬ AtPosition parameter input position) :
    SettlingTrace parameter otsSecret ftsSecret f queries := by
  intro n input hinput cache hf hcached position hat
  exact False.elim (h input (List.mem_of_getElem? hinput) position hat)

theorem SettlingRun.pure {α : Type} (value : α) :
    SettlingRun parameter otsSecret ftsSecret f (pure value) := SettlingTrace.nil

theorem SettlingRun.bind {α β : Type} {computation : OracleComp HashSpec α}
    {next : α → OracleComp HashSpec β}
    (hleft : SettlingRun parameter otsSecret ftsSecret f computation)
    (hright : SettlingRun parameter otsSecret ftsSecret f (next (evalWithAnswerFn f computation))) :
    SettlingRun parameter otsSecret ftsSecret f (computation >>= next) := by
  unfold SettlingRun
  rw [queriedInputs_bind]
  exact hleft.append hright

theorem SettlingRun.tweakableHash_after {α : Type} (position : Position)
    (computation : OracleComp HashSpec α) (payload : α → HashInput)
    (hbefore : SettlingRun parameter otsSecret ftsSecret f computation)
    (hsettles : ∀ (cache : QueryCache HashSpec), cache.AgreesWithFn f →
      CachedRun cache f (do
        let value ← computation
        Concrete.tweakableHash parameter position.domain (payload value)) →
      Settled parameter otsSecret ftsSecret cache position) :
    SettlingRun parameter otsSecret ftsSecret f (do
      let value ← computation
      Concrete.tweakableHash parameter position.domain (payload value)) := by
  unfold SettlingRun
  rw [queriedInputs_bind, queriedInputs_tweakableHash]
  apply hbefore.snoc
  intro cache hf hcached other hat
  have heq : other = position := atPosition_unique parameter hat ⟨_, rfl⟩
  subst other
  apply hsettles cache hf
  intro input hinput
  rw [queriedInputs_bind, queriedInputs_tweakableHash] at hinput
  exact hcached input hinput

theorem SettlingRun.sequenceFin {α : Type} {n : Nat}
    (computation : Fin n → OracleComp HashSpec α)
    (h : ∀ index, SettlingRun parameter otsSecret ftsSecret f (computation index)) :
    SettlingRun parameter otsSecret ftsSecret f (Concrete.sequenceFin computation) := by
  induction n with
  | zero => exact SettlingRun.pure _
  | succ n ih =>
      rw [Concrete.sequenceFin]
      exact (h 0).bind ((ih (fun i => computation i.succ) (fun i => h i.succ)).bind (SettlingRun.pure _))

theorem SettlingTrace.settled_of_prefix {queries before after : List HashInput}
    (h : SettlingTrace parameter otsSecret ftsSecret f queries) (hsplit : queries = before ++ after)
    {cache : QueryCache HashSpec} (hf : cache.AgreesWithFn f)
    (hcached : ∀ input ∈ before, cache input ≠ none)
    {input : HashInput} (hinput : input ∈ before) {position : Position}
    (hat : AtPosition parameter input position) : Settled parameter otsSecret ftsSecret cache position := by
  obtain ⟨n, hn, heq⟩ := List.getElem_of_mem hinput
  have hget : queries[n]? = some input := by
    rw [hsplit, List.getElem?_append_left hn, List.getElem?_eq_getElem hn, heq]
  apply h n input hget cache hf _ position hat
  intro prior hprior
  rw [hsplit, List.take_append_of_le_length (by omega)] at hprior
  exact hcached prior (List.mem_of_mem_take hprior)

end SphincsSecurity

import SphincsSecurity.Proof.OtsProbeNativeSupportedRootReserve

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def LiveResolvedQueryBound (predicate : LazyRevealProbe.Query Coordinate → Prop)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    Nat → DeferredContext → Nat → (OtsSecretIndex → HashOutput) → Prop :=
  OracleComp.construct (fun _ _ _ _ _ => True)
    (fun input _ next q context fuel table => DeferredCompletable table context →
      (predicate input → 0 < q) ∧
        ∀ result, some result ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input))) →
          next result.value (if predicate input then q - 1 else q) result.context result.remaining result.table) computation

theorem liveResolvedQueryBound_query_bind
    (predicate : LazyRevealProbe.Query Coordinate → Prop) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    LiveResolvedQueryBound predicate ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next)
      q context fuel table ↔
      (DeferredCompletable table context → (predicate input → 0 < q) ∧
        ∀ result, some result ∈ support (runResolvedFromTable context fuel table (liftM (OracleSpec.query input))) →
          LiveResolvedQueryBound predicate (next result.value) (if predicate input then q - 1 else q)
            result.context result.remaining result.table) := Iff.rfl

theorem liveResolvedQueryBound_of_not_completable
    (predicate : LazyRevealProbe.Query Coordinate → Prop) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hnot : ¬DeferredCompletable table context) : LiveResolvedQueryBound predicate computation q context fuel table := by
  induction computation using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind input next _ => intro hcomplete; exact (hnot hcomplete).elim

theorem LiveResolvedQueryBound.mono
    {predicate : LazyRevealProbe.Query Coordinate → Prop} {computation : OracleComp (LazyRevealProbe.World Coordinate) α}
    {q r : Nat} {context : DeferredContext} {fuel : Nat} {table : OtsSecretIndex → HashOutput}
    (hbound : LiveResolvedQueryBound predicate computation q context fuel table) (hle : q ≤ r) :
    LiveResolvedQueryBound predicate computation r context fuel table := by
  induction computation using OracleComp.inductionOn generalizing q r context fuel table with
  | pure value => trivial
  | query_bind input next ih =>
      rw [liveResolvedQueryBound_query_bind] at hbound ⊢
      intro hcomplete
      have hbound := hbound hcomplete
      refine ⟨fun hinput => (hbound.1 hinput).trans_le hle, ?_⟩
      intro result hresult
      exact ih result.value (hbound.2 result hresult) (by split_ifs <;> omega)

theorem liveResolvedQueryBound_of_syntactic
    (predicate : LazyRevealProbe.Query Coordinate → Prop) [DecidablePred predicate] (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q : Nat) (hbound : computation.IsQueryBoundP predicate q)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    LiveResolvedQueryBound predicate computation q context fuel table := by
  induction computation using OracleComp.inductionOn generalizing q context fuel table with
  | pure value => trivial
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [liveResolvedQueryBound_query_bind]
      intro _
      refine ⟨fun hinput => hbound.1.resolve_left (not_not.mpr hinput), ?_⟩
      intro result _
      by_cases hinput : predicate input
      · simp only [if_pos hinput] at hbound ⊢
        exact ih result.value _ (hbound.2 result.value) result.context result.remaining result.table
      · simp only [if_neg hinput] at hbound ⊢
        exact ih result.value _ (hbound.2 result.value) result.context result.remaining result.table

theorem liveResolvedQueryBound_bind_of_syntactic_prefix
    (predicate : LazyRevealProbe.Query Coordinate → Prop) [DecidablePred predicate]
    (left : OracleComp (LazyRevealProbe.World Coordinate) α) (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (q r : Nat) (hleft : left.IsQueryBoundP predicate q)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hnext : ∀ result, some result ∈ support (runResolvedFromTable context fuel table left) →
      LiveResolvedQueryBound predicate (next result.value) r result.context result.remaining result.table) :
    LiveResolvedQueryBound predicate (left >>= next) (q + r) context fuel table := by
  induction left using OracleComp.inductionOn generalizing q context fuel table with
  | pure value =>
      exact (hnext ⟨context, fuel, value, table⟩ (by simp [runResolvedFromTable])).mono (Nat.le_add_left _ _)
  | query_bind input continuation ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hleft
      rw [bind_assoc, liveResolvedQueryBound_query_bind]
      intro _
      have hpositive : predicate input → 0 < q := by intro hinput; simpa [hinput] using hleft.1
      refine ⟨fun hinput => by have := hpositive hinput; omega, ?_⟩
      intro middle hmiddle
      have htail : LiveResolvedQueryBound predicate (continuation middle.value >>= next)
          ((if predicate input then q - 1 else q) + r) middle.context middle.remaining middle.table := by
        apply ih middle.value _ (hleft.2 middle.value) middle.context middle.remaining middle.table
        intro result hresult
        apply hnext result
        rw [runResolvedFromTable_bind, mem_support_bind_iff]
        exact ⟨some middle, hmiddle, hresult⟩
      convert htail using 1
      by_cases hinput : predicate input
      · simp only [if_pos hinput]
        have := hpositive hinput
        omega
      · simp only [if_neg hinput]

theorem LiveResolvedQueryBound.of_imp
    {predicate weaker : LazyRevealProbe.Query Coordinate → Prop} {computation : OracleComp (LazyRevealProbe.World Coordinate) α}
    {q : Nat} {context : DeferredContext} {fuel : Nat} {table : OtsSecretIndex → HashOutput}
    (himp : ∀ input, weaker input → predicate input)
    (hbound : LiveResolvedQueryBound predicate computation q context fuel table) :
    LiveResolvedQueryBound weaker computation q context fuel table := by
  induction computation using OracleComp.inductionOn generalizing q context fuel table with
  | pure value => trivial
  | query_bind input next ih =>
      rw [liveResolvedQueryBound_query_bind] at hbound ⊢
      intro hcomplete
      have hbound := hbound hcomplete
      refine ⟨fun hinput => hbound.1 (himp input hinput), ?_⟩
      intro result hresult
      apply (ih result.value (hbound.2 result hresult)).mono
      by_cases hweaker : weaker input
      · simp only [if_pos hweaker, if_pos (himp input hweaker)]
        exact le_rfl
      · simp only [if_neg hweaker]
        split_ifs <;> omega

end SphincsSecurity.Concrete.OtsProbeSimulation

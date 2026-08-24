import SphincsSecurity.Proof.Settled
import SphincsSecurity.Proof.Slot

/-!
# The bad event and what pays for it

`Bad` is the event the reduction charges: a settled position, its honest input cached, and another
cached input at the same tweak whose answer agrees with it after truncation. It is a property of the
cache alone, which is what lets the accounting of `Amortized` bound it.

The potential is one unit per cached input at an unsettled position's tweak, plus one for each of
that position's children still unsettled. The first pays for the answer that settles the position,
which has to miss every input already cached at its tweak; the second pays for the answer that fixes
the honest input one level up, which may find it already cached.

This module also proves what makes the charge finite: with one query, only the position of the queried
input can become settled, unless its parent does.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

/-- The input is hashed at the position's tweak. -/
def AtPosition (input : HashInput) (p : Position) : Prop :=
  ∃ payload, input = tweakableHashInput parameter p.domain payload

theorem atPosition_honestInput (f : QueryImpl HashSpec Id) (p : Position) :
    AtPosition parameter (honestInput f parameter otsSecret ftsSecret p) p :=
  ⟨_, rfl⟩

theorem atPosition_cachedInput (cache : QueryCache HashSpec) (p : Position) :
    AtPosition parameter (cachedInput parameter otsSecret ftsSecret cache p) p :=
  ⟨_, rfl⟩

/-- **A tweak names one position.** -/
theorem atPosition_unique {input : HashInput} {p q : Position} (hp : AtPosition parameter input p)
    (hq : AtPosition parameter input q) : p = q := by
  obtain ⟨payload, hpayload⟩ := hp
  obtain ⟨payload', hpayload'⟩ := hq
  exact Position.domain_injective (tweakableHashInput_injective parameter
    (Position.domain_inRange p) (Position.domain_inRange q) (hpayload ▸ hpayload')).1

theorem atPosition_ne {input input' : HashInput} {p q : Position} (hp : AtPosition parameter input p)
    (hq : AtPosition parameter input' q) (hne : p ≠ q) : input ≠ input' := fun heq =>
  hne (atPosition_unique parameter hp (heq ▸ hq))

/-- The cache holds a hit: a settled position whose honest answer another cached input at the same
tweak reproduces after truncation. -/
def Bad (cache : QueryCache HashSpec) : Prop :=
  ∃ p : Position, Settled parameter otsSecret ftsSecret cache p ∧ ∃ input ax ay,
    AtPosition parameter input p ∧ input ≠ cachedInput parameter otsSecret ftsSecret cache p
      ∧ cache input = some ax
      ∧ cache (cachedInput parameter otsSecret ftsSecret cache p) = some ay
      ∧ truncateHash ax = truncateHash ay

/-! ### One fresh query -/

theorem le_cacheQuery {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput}
    (huncached : cache input = none) : cache ≤ cache.cacheQuery input answer := by
  intro x u hx
  by_cases hxeq : x = input
  · rw [hxeq, huncached] at hx
    simp at hx
  · rwa [QueryCache.cacheQuery_of_ne _ _ hxeq]

/-- **Only the queried position can settle.** A fresh query settles no position other than the one
its input is at, unless it settles that position's parent. -/
theorem settled_of_settled_cacheQuery {cache : QueryCache HashSpec} {input₀ : HashInput}
    {answer : HashOutput} (huncached : cache input₀ = none) {p₀ : Option Position}
    (hposition : ∀ q, AtPosition parameter input₀ q → p₀ = some q)
    (hparent : ∀ q q₁, p₀ = some q → Position.parentOf q = some q₁ →
      ¬ Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) q₁) :
    ∀ (n : Nat) (q : Position), q.depth < n → p₀ ≠ some q →
      Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) q →
      Settled parameter otsSecret ftsSecret cache q := by
  have hle := le_cacheQuery (cache := cache) (input := input₀) (answer := answer) huncached
  intro n
  induction n with
  | zero => intro q hdepth; omega
  | succ n ih =>
      intro q hdepth hne hsettled
      have hchildren : ∀ c ∈ q.children, Settled parameter otsSecret ftsSecret cache c := by
        intro c hc
        have hcne : p₀ ≠ some c := by
          intro hcp
          exact hparent c q hcp (Position.mem_children_iff.mp hc) hsettled
        exact ih c (by have := Position.depth_lt_of_mem_children hc; omega) hcne
          (hsettled.children c hc)
      have hvalues : ∀ c ∈ q.children,
          honestValue (fromCache (cache.cacheQuery input₀ answer)) parameter otsSecret ftsSecret c
            = honestValue (fromCache cache) parameter otsSecret ftsSecret c := fun c hc =>
        honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hle) (hchildren c hc)
      have hinput : cachedInput parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) q
          = cachedInput parameter otsSecret ftsSecret cache q :=
        honestInput_congr _ _ parameter otsSecret ftsSecret hsettled.valid hvalues
      have hcached := hsettled.cached
      rw [hinput] at hcached
      have hinputne : cachedInput parameter otsSecret ftsSecret cache q ≠ input₀ := by
        intro heq
        exact hne (hposition q (heq ▸ atPosition_cachedInput parameter otsSecret ftsSecret cache q))
      rw [QueryCache.cacheQuery_of_ne _ _ hinputne] at hcached
      rw [settled_iff]
      exact ⟨hsettled.valid, hcached, hchildren⟩

/-! ### The potential -/

/-- The inputs the cache holds at a position's tweak. -/
def cachedAt (cache : QueryCache HashSpec) (p : Position) : Set HashInput :=
  {input | cache input ≠ none ∧ AtPosition parameter input p}

/-- The cache holds finitely many inputs. Every cache a run produces does, and the accounting needs
it to count. -/
def Finite (cache : QueryCache HashSpec) : Prop := {input | cache input ≠ none}.Finite

theorem finite_cacheQuery {cache : QueryCache HashSpec} (hfinite : Finite cache)
    (input : HashInput) (answer : HashOutput) : Finite (cache.cacheQuery input answer) := by
  refine Set.Finite.subset (hfinite.insert input) fun x hx => ?_
  by_cases hxeq : x = input
  · exact Set.mem_insert_iff.mpr (Or.inl hxeq)
  · refine Set.mem_insert_iff.mpr (Or.inr ?_)
    simpa only [Set.mem_setOf_eq, QueryCache.cacheQuery_of_ne _ _ hxeq] using hx

theorem cachedAt_finite {cache : QueryCache HashSpec} (hfinite : Finite cache) (p : Position) :
    (cachedAt parameter cache p).Finite :=
  hfinite.subset fun _ hx => hx.1

/-- The children of a position the cache has not settled. -/
def unsettledChildren (cache : QueryCache HashSpec) (p : Position) : Set Position :=
  {c | c ∈ p.children ∧ ¬ Settled parameter otsSecret ftsSecret cache c}

theorem unsettledChildren_finite (cache : QueryCache HashSpec) (p : Position) :
    (unsettledChildren parameter otsSecret ftsSecret cache p).Finite :=
  (p.children.finite_toSet).subset fun _ hc => hc.1

/-- **What pays for the charges.** Per cached input at an unsettled position's tweak, one unit for
the answer that will settle the position, which has to miss every input already cached there, and one
for each child still unsettled, for the answer that fixes the honest input one level up. -/
noncomputable def potential (cache : QueryCache HashSpec) : Nat :=
  open Classical in
  ∑ p : Position, if Settled parameter otsSecret ftsSecret cache p then 0
    else (cachedAt parameter cache p).ncard
      * (1 + (unsettledChildren parameter otsSecret ftsSecret cache p).ncard)

/-! ### How one query moves the pieces -/

theorem cachedAt_cacheQuery_of_not_atPosition {cache : QueryCache HashSpec} {input₀ : HashInput}
    {answer : HashOutput} {p : Position} (hp : ¬ AtPosition parameter input₀ p) :
    cachedAt parameter (cache.cacheQuery input₀ answer) p = cachedAt parameter cache p := by
  ext x
  by_cases hxeq : x = input₀
  · subst hxeq
    simp only [cachedAt, Set.mem_setOf_eq, QueryCache.cacheQuery_self]
    exact ⟨fun hx => absurd hx.2 hp, fun hx => absurd hx.2 hp⟩
  · simp only [cachedAt, Set.mem_setOf_eq, QueryCache.cacheQuery_of_ne _ _ hxeq]

theorem cachedAt_cacheQuery_self {cache : QueryCache HashSpec} {input₀ : HashInput}
    {answer : HashOutput} {p : Position} (hp : AtPosition parameter input₀ p) :
    cachedAt parameter (cache.cacheQuery input₀ answer) p
      = insert input₀ (cachedAt parameter cache p) := by
  ext x
  by_cases hxeq : x = input₀
  · subst hxeq
    simp only [cachedAt, Set.mem_setOf_eq, QueryCache.cacheQuery_self, Set.mem_insert_iff,
      true_or, ne_eq, reduceCtorEq, not_false_eq_true, hp, and_self]
  · simp only [cachedAt, Set.mem_setOf_eq, QueryCache.cacheQuery_of_ne _ _ hxeq,
      Set.mem_insert_iff, hxeq, false_or]

theorem unsettledChildren_subset {cache cache' : QueryCache HashSpec} (hle : cache ≤ cache')
    (p : Position) :
    unsettledChildren parameter otsSecret ftsSecret cache' p
      ⊆ unsettledChildren parameter otsSecret ftsSecret cache p := fun _ hc =>
  ⟨hc.1, fun hsettled => hc.2 (hsettled.mono hle)⟩

theorem unsettledChildren_ncard_mono {cache cache' : QueryCache HashSpec} (hle : cache ≤ cache')
    (p : Position) :
    (unsettledChildren parameter otsSecret ftsSecret cache' p).ncard
      ≤ (unsettledChildren parameter otsSecret ftsSecret cache p).ncard :=
  Set.ncard_le_ncard (unsettledChildren_subset parameter otsSecret ftsSecret hle p)
    (unsettledChildren_finite parameter otsSecret ftsSecret cache p)

/-- A child that settles is a unit released at its parent, for every input cached there. -/
theorem unsettledChildren_ncard_lt {cache cache' : QueryCache HashSpec} (hle : cache ≤ cache')
    {p c : Position} (hmem : c ∈ p.children)
    (hunsettled : ¬ Settled parameter otsSecret ftsSecret cache c)
    (hsettled : Settled parameter otsSecret ftsSecret cache' c) :
    (unsettledChildren parameter otsSecret ftsSecret cache' p).ncard + 1
      ≤ (unsettledChildren parameter otsSecret ftsSecret cache p).ncard := by
  refine Set.ncard_lt_ncard ⟨unsettledChildren_subset parameter otsSecret ftsSecret hle p, ?_⟩
    (unsettledChildren_finite parameter otsSecret ftsSecret cache p)
  intro hsubset
  exact (hsubset ⟨hmem, hunsettled⟩).2 hsettled

end SphincsSecurity

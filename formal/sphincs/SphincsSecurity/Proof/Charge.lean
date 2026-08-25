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

/-- A cached collision with the honest value at a settled position is `Bad`. -/
theorem bad_of_settled_collision {cache : QueryCache HashSpec} {f : QueryImpl HashSpec Id}
    (hf : cache.AgreesWithFn f) {p : Position}
    (hsettled : Settled parameter otsSecret ftsSecret cache p) {input : HashInput}
    (hposition : AtPosition parameter input p)
    (hne : input ≠ honestInput f parameter otsSecret ftsSecret p)
    (hcached : cache input ≠ none)
    (hvalue : truncateHash (f input) = honestValue f parameter otsSecret ftsSecret p) :
    Bad parameter otsSecret ftsSecret cache := by
  obtain ⟨ax, hax⟩ := Option.ne_none_iff_exists'.mp hcached
  obtain ⟨ay, hay⟩ := Option.ne_none_iff_exists'.mp hsettled.cached
  have hpinned := honestInput_eq_cachedInput hf hsettled
  refine ⟨p, hsettled, input, ax, ay, hposition, ?_, hax, hay, ?_⟩
  · rwa [hpinned] at hne
  · rw [← hf hax, ← hf hay, hvalue, honestValue, hpinned]

theorem bad_of_settled_payload_collision {cache : QueryCache HashSpec}
    {f : QueryImpl HashSpec Id} (hf : cache.AgreesWithFn f) {p : Position}
    (hsettled : Settled parameter otsSecret ftsSecret cache p) {payload : HashInput}
    (hpayload : payload ≠ honestPayload f parameter otsSecret ftsSecret p)
    (hcached : cache (tweakableHashInput parameter p.domain payload) ≠ none)
    (hvalue : truncateHash (f (tweakableHashInput parameter p.domain payload))
      = honestValue f parameter otsSecret ftsSecret p) :
    Bad parameter otsSecret ftsSecret cache := by
  apply bad_of_settled_collision parameter otsSecret ftsSecret hf hsettled
    (hposition := ⟨payload, rfl⟩) (hcached := hcached) (hvalue := hvalue)
  intro heq
  apply hpayload
  exact (tweakableHashInput_injective parameter (Position.domain_inRange p)
    (Position.domain_inRange p) (by simpa [honestInput] using heq)).2

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

/-- Querying another input at an already settled position settles nothing new. -/
theorem settled_of_cacheQuery_at_settled {cache : QueryCache HashSpec} {input₀ : HashInput}
    {answer : HashOutput} {p₀ : Position} (huncached : cache input₀ = none)
    (hposition : AtPosition parameter input₀ p₀)
    (hsettled₀ : Settled parameter otsSecret ftsSecret cache p₀) :
    ∀ (n : Nat) (p : Position), p.depth < n →
      Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p →
      Settled parameter otsSecret ftsSecret cache p := by
  have hle := le_cacheQuery (cache := cache) (input := input₀) (answer := answer) huncached
  intro n
  induction n with
  | zero => intro p hdepth; omega
  | succ n ih =>
      intro p hdepth hsettled
      by_cases hp : p = p₀
      · simpa [hp] using hsettled₀
      · have hchildren : ∀ c ∈ p.children, Settled parameter otsSecret ftsSecret cache c := by
          intro c hc
          exact ih c (by have := Position.depth_lt_of_mem_children hc; omega)
            (hsettled.children c hc)
        have hvalues : ∀ c ∈ p.children,
            honestValue (fromCache (cache.cacheQuery input₀ answer)) parameter otsSecret ftsSecret c
              = honestValue (fromCache cache) parameter otsSecret ftsSecret c := fun c hc =>
          honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hle) (hchildren c hc)
        have hinput : cachedInput parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p
            = cachedInput parameter otsSecret ftsSecret cache p :=
          honestInput_congr _ _ parameter otsSecret ftsSecret hsettled.valid hvalues
        have hinputne : cachedInput parameter otsSecret ftsSecret cache p ≠ input₀ :=
          atPosition_ne parameter (atPosition_cachedInput parameter otsSecret ftsSecret cache p)
            hposition hp
        rw [settled_iff]
        refine ⟨hsettled.valid, ?_, hchildren⟩
        have hcached := hsettled.cached
        rw [hinput, QueryCache.cacheQuery_of_ne _ _ hinputne] at hcached
        exact hcached

/-- Below the queried position, a fresh query settles nothing. -/
theorem settled_of_cacheQuery_below {cache : QueryCache HashSpec} {input₀ : HashInput}
    {answer : HashOutput} {p₀ : Position} (huncached : cache input₀ = none)
    (hposition : AtPosition parameter input₀ p₀) :
    ∀ (n : Nat) (p : Position), p.depth < n → p.depth < p₀.depth →
      Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p →
      Settled parameter otsSecret ftsSecret cache p := by
  have hle := le_cacheQuery (cache := cache) (input := input₀) (answer := answer) huncached
  intro n
  induction n with
  | zero => intro p hdepth; omega
  | succ n ih =>
      intro p hdepth hbelow hsettled
      have hp : p ≠ p₀ := by intro heq; subst heq; omega
      have hchildren : ∀ c ∈ p.children, Settled parameter otsSecret ftsSecret cache c := by
        intro c hc
        exact ih c (by have := Position.depth_lt_of_mem_children hc; omega)
          (by have := Position.depth_lt_of_mem_children hc; omega) (hsettled.children c hc)
      have hvalues : ∀ c ∈ p.children,
          honestValue (fromCache (cache.cacheQuery input₀ answer)) parameter otsSecret ftsSecret c
            = honestValue (fromCache cache) parameter otsSecret ftsSecret c := fun c hc =>
        honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hle) (hchildren c hc)
      have hinput : cachedInput parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p
          = cachedInput parameter otsSecret ftsSecret cache p :=
        honestInput_congr _ _ parameter otsSecret ftsSecret hsettled.valid hvalues
      have hinputne : cachedInput parameter otsSecret ftsSecret cache p ≠ input₀ :=
        atPosition_ne parameter (atPosition_cachedInput parameter otsSecret ftsSecret cache p)
          hposition hp
      rw [settled_iff]
      refine ⟨hsettled.valid, ?_, hchildren⟩
      have hcached := hsettled.cached
      rw [hinput, QueryCache.cacheQuery_of_ne _ _ hinputne] at hcached
      exact hcached

/-- If a fresh query settles its own previously unsettled position, it was the honest input and all
children were settled before the query. -/
theorem eq_cachedInput_and_children_of_settled_cacheQuery {cache : QueryCache HashSpec}
    {input₀ : HashInput} {answer : HashOutput} {p₀ : Position}
    (huncached : cache input₀ = none) (hposition : AtPosition parameter input₀ p₀)
    (hunsettled : ¬ Settled parameter otsSecret ftsSecret cache p₀)
    (hsettled : Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p₀) :
    input₀ = cachedInput parameter otsSecret ftsSecret cache p₀
      ∧ ∀ c ∈ p₀.children, Settled parameter otsSecret ftsSecret cache c := by
  have hle := le_cacheQuery (cache := cache) (input := input₀) (answer := answer) huncached
  have hchildren : ∀ c ∈ p₀.children, Settled parameter otsSecret ftsSecret cache c := by
    intro c hc
    exact settled_of_cacheQuery_below parameter otsSecret ftsSecret huncached hposition
      (c.depth + 1) c (by omega) (Position.depth_lt_of_mem_children hc) (hsettled.children c hc)
  have hvalues : ∀ c ∈ p₀.children,
      honestValue (fromCache (cache.cacheQuery input₀ answer)) parameter otsSecret ftsSecret c
        = honestValue (fromCache cache) parameter otsSecret ftsSecret c := fun c hc =>
    honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hle) (hchildren c hc)
  have hinput : cachedInput parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p₀
      = cachedInput parameter otsSecret ftsSecret cache p₀ :=
    honestInput_congr _ _ parameter otsSecret ftsSecret hsettled.valid hvalues
  refine ⟨?_, hchildren⟩
  by_contra hne
  apply hunsettled
  rw [settled_iff]
  refine ⟨hsettled.valid, ?_, hchildren⟩
  have hcached := hsettled.cached
  have hne' : cachedInput parameter otsSecret ftsSecret cache p₀ ≠ input₀ :=
    fun h => hne h.symm
  rw [hinput, QueryCache.cacheQuery_of_ne _ _ hne'] at hcached
  exact hcached

theorem honestValue_cacheQuery_self_of_settled {cache : QueryCache HashSpec}
    {input₀ : HashInput} {answer : HashOutput} {p₀ : Position}
    (huncached : cache input₀ = none) (hposition : AtPosition parameter input₀ p₀)
    (hunsettled : ¬ Settled parameter otsSecret ftsSecret cache p₀)
    (hsettled : Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p₀) :
    honestValue (fromCache (cache.cacheQuery input₀ answer)) parameter otsSecret ftsSecret p₀
      = truncateHash answer := by
  obtain ⟨hinput₀, hchildren⟩ := eq_cachedInput_and_children_of_settled_cacheQuery
    parameter otsSecret ftsSecret huncached hposition hunsettled hsettled
  have hle := le_cacheQuery (cache := cache) (input := input₀) (answer := answer) huncached
  have hvalues : ∀ c ∈ p₀.children,
      honestValue (fromCache (cache.cacheQuery input₀ answer)) parameter otsSecret ftsSecret c
        = honestValue (fromCache cache) parameter otsSecret ftsSecret c := fun c hc =>
    honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hle) (hchildren c hc)
  have hinput : cachedInput parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p₀
      = cachedInput parameter otsSecret ftsSecret cache p₀ :=
    honestInput_congr _ _ parameter otsSecret ftsSecret hsettled.valid hvalues
  change truncateHash (fromCache (cache.cacheQuery input₀ answer)
    (cachedInput parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p₀))
      = truncateHash answer
  rw [hinput, ← hinput₀]
  simp [fromCache]

/-! ### The potential -/

/-- The inputs the cache holds at a position's tweak. -/
def cachedAt (cache : QueryCache HashSpec) (p : Position) : Set HashInput :=
  {input | cache input ≠ none ∧ AtPosition parameter input p}

/-- The cache holds finitely many inputs. Every cache a run produces does, and the accounting needs
it to count. -/
def Finite (cache : QueryCache HashSpec) : Prop := {input | cache input ≠ none}.Finite

theorem finite_empty : Finite (∅ : QueryCache HashSpec) := by
  simp [Finite]

theorem not_bad_empty : ¬ Bad parameter otsSecret ftsSecret (∅ : QueryCache HashSpec) := by
  rintro ⟨p, _, input, ax, ay, _, _, hcached, _⟩
  simp at hcached

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

/-- Truncated answers already cached at a position. -/
noncomputable def answerTargets (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (p : Position) : Finset Digest :=
  open Classical in
  (cachedAt_finite parameter hfinite p).toFinset.image fun input =>
    truncateHash ((cache input).getD 0)

theorem answerTargets_card_le (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (p : Position) :
    (answerTargets parameter cache hfinite p).card ≤ (cachedAt parameter cache p).ncard := by
  rw [answerTargets]
  refine (Finset.card_image_le.trans_eq ?_)
  exact (Set.ncard_eq_toFinset_card _ (cachedAt_finite parameter hfinite p)).symm

theorem mem_answerTargets {cache : QueryCache HashSpec} (hfinite : Finite cache) {p : Position}
    {input : HashInput} (hinput : input ∈ cachedAt parameter cache p) :
    truncateHash ((cache input).getD 0) ∈ answerTargets parameter cache hfinite p := by
  classical
  rw [answerTargets]
  exact Finset.mem_image.mpr ⟨input,
    (cachedAt_finite parameter hfinite p).mem_toFinset.mpr hinput, rfl⟩

/-- Payload blocks of cached inputs at a parent, at the slot occupied by one of its children. -/
noncomputable def slotTargets (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (child parent : Position) : Finset Digest :=
  open Classical in
  (cachedAt_finite parameter hfinite parent).toFinset.image fun input =>
    slotDigest (parent.children.idxOf child) input

theorem slotTargets_card_le (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (child parent : Position) :
    (slotTargets parameter cache hfinite child parent).card
      ≤ (cachedAt parameter cache parent).ncard := by
  rw [slotTargets]
  refine (Finset.card_image_le.trans_eq ?_)
  exact (Set.ncard_eq_toFinset_card _ (cachedAt_finite parameter hfinite parent)).symm

theorem mem_slotTargets {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {child parent : Position} {input : HashInput} (hinput : input ∈ cachedAt parameter cache parent) :
    slotDigest (parent.children.idxOf child) input
      ∈ slotTargets parameter cache hfinite child parent := by
  classical
  rw [slotTargets]
  exact Finset.mem_image.mpr ⟨input,
    (cachedAt_finite parameter hfinite parent).mem_toFinset.mpr hinput, rfl⟩

/-- Avoiding a child's slot targets prevents that query from settling the child's parent. -/
theorem not_settled_parent_of_avoids_slotTargets {cache : QueryCache HashSpec}
    (hfinite : Finite cache) {input₀ : HashInput} {answer : HashOutput} {parent child : Position}
    (huncached : cache input₀ = none) (hposition : AtPosition parameter input₀ child)
    (hunsettled : ¬ Settled parameter otsSecret ftsSecret cache child)
    (hsettled : Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) child)
    (hmem : child ∈ parent.children)
    (havoid : truncateHash answer ∉ slotTargets parameter cache hfinite child parent) :
    ¬ Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) parent := by
  intro hparent
  have hpne : parent ≠ child := by
    intro heq
    subst heq
    have := Position.depth_lt_of_mem_children hmem
    omega
  have hinputne : cachedInput parameter otsSecret ftsSecret
      (cache.cacheQuery input₀ answer) parent ≠ input₀ :=
    atPosition_ne parameter
      (atPosition_cachedInput parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) parent)
      hposition hpne
  have hcached := hparent.cached
  rw [QueryCache.cacheQuery_of_ne _ _ hinputne] at hcached
  have hat : cachedInput parameter otsSecret ftsSecret
      (cache.cacheQuery input₀ answer) parent ∈ cachedAt parameter cache parent :=
    ⟨hcached, atPosition_cachedInput parameter otsSecret ftsSecret
      (cache.cacheQuery input₀ answer) parent⟩
  apply havoid
  have hslot := slotDigest_honestInput_child (fromCache (cache.cacheQuery input₀ answer))
    parameter otsSecret ftsSecret hparent.valid hmem
  have hvalue := honestValue_cacheQuery_self_of_settled parameter otsSecret ftsSecret
    huncached hposition hunsettled hsettled
  rw [hvalue] at hslot
  rw [← hslot]
  exact mem_slotTargets parameter hfinite hat

/-- The targets charged when a query settles its own position. -/
noncomputable def settlingTargets (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (p : Position) : Finset Digest :=
  match p.parentOf with
  | none => answerTargets parameter cache hfinite p
  | some parent => answerTargets parameter cache hfinite p ∪
      slotTargets parameter cache hfinite p parent

theorem settlingTargets_card_le (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (p : Position) :
    (settlingTargets parameter cache hfinite p).card ≤ (cachedAt parameter cache p).ncard
      + match p.parentOf with
        | none => 0
        | some parent => (cachedAt parameter cache parent).ncard := by
  rw [settlingTargets]
  split
  · simpa using answerTargets_card_le parameter cache hfinite p
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add
      (answerTargets_card_le parameter cache hfinite p)
      (slotTargets_card_le parameter cache hfinite p _))

/-- The children of a position the cache has not settled. -/
def unsettledChildren (cache : QueryCache HashSpec) (p : Position) : Set Position :=
  {c | c ∈ p.children ∧ ¬ Settled parameter otsSecret ftsSecret cache c}

theorem unsettledChildren_finite (cache : QueryCache HashSpec) (p : Position) :
    (unsettledChildren parameter otsSecret ftsSecret cache p).Finite :=
  (p.children.finite_toSet).subset fun _ hc => hc.1

/-- No position has more unsettled children than the widest payload has slots. -/
theorem unsettledChildren_ncard_le (cache : QueryCache HashSpec) (p : Position) :
    (unsettledChildren parameter otsSecret ftsSecret cache p).ncard ≤ numChains := by
  calc
    _ ≤ (p.children.toFinset : Set Position).ncard := Set.ncard_le_ncard (by
      intro c hc
      simpa using hc.1) (Finset.finite_toSet p.children.toFinset)
    _ = p.children.toFinset.card := by
      classical
      rw [Set.ncard_eq_toFinset_card _ (Finset.finite_toSet p.children.toFinset)]
      congr 1
      ext c
      simp
    _ ≤ p.children.length := List.toFinset_card_le p.children
    _ ≤ numChains := Position.children_length_le p

/-- The summand of `potential` at one position. -/
noncomputable def contribution (cache : QueryCache HashSpec) (p : Position) : Nat :=
  open Classical in
  if Settled parameter otsSecret ftsSecret cache p then 0
    else (cachedAt parameter cache p).ncard
      * (1 + (unsettledChildren parameter otsSecret ftsSecret cache p).ncard)

/-- **What pays for the charges.** Per cached input at an unsettled position's tweak, one unit for
the answer that will settle the position, which has to miss every input already cached there, and one
for each child still unsettled, for the answer that fixes the honest input one level up. -/
noncomputable def potential (cache : QueryCache HashSpec) : Nat :=
  open Classical in
  ∑ p : Position, contribution parameter otsSecret ftsSecret cache p

theorem potential_empty :
    potential parameter otsSecret ftsSecret (∅ : QueryCache HashSpec) = 0 := by
  classical
  rw [potential]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [contribution]
  split
  · rfl
  · have hcachedAt : cachedAt parameter (∅ : QueryCache HashSpec) p = ∅ := by
      ext input
      simp [cachedAt]
    rw [hcachedAt, Set.ncard_empty, Nat.zero_mul]

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

/-- Away from the queried position, extending a cache can only release potential. -/
theorem contribution_le_of_cachedAt_eq {cache cache' : QueryCache HashSpec} (hle : cache ≤ cache')
    (p : Position) (hcachedAt : cachedAt parameter cache' p = cachedAt parameter cache p) :
    contribution parameter otsSecret ftsSecret cache' p
      ≤ contribution parameter otsSecret ftsSecret cache p := by
  by_cases hsettled : Settled parameter otsSecret ftsSecret cache p
  · have hsettled' := hsettled.mono hle
    simp [contribution, hsettled, hsettled']
  · by_cases hsettled' : Settled parameter otsSecret ftsSecret cache' p
    · simp [contribution, hsettled, hsettled']
    · simp only [contribution, hsettled, hsettled', if_false, hcachedAt]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_left
        (unsettledChildren_ncard_mono parameter otsSecret ftsSecret hle p) 1)

/-- Settling a position whose children were settled releases its base unit at every cached input. -/
theorem contribution_add_cachedAt_le_of_settled {cache cache' : QueryCache HashSpec}
    {p : Position} (hunsettled : ¬ Settled parameter otsSecret ftsSecret cache p)
    (hsettled : Settled parameter otsSecret ftsSecret cache' p)
    (hchildren : ∀ c ∈ p.children, Settled parameter otsSecret ftsSecret cache c) :
    contribution parameter otsSecret ftsSecret cache' p + (cachedAt parameter cache p).ncard
      ≤ contribution parameter otsSecret ftsSecret cache p := by
  have hempty : unsettledChildren parameter otsSecret ftsSecret cache p = ∅ := by
    ext c
    constructor
    · intro hc
      exact (hc.2 (hchildren c hc.1)).elim
    · simp
  simp [contribution, hunsettled, hsettled, hempty]

/-- When a child settles, each cached input at its parent releases one child-slot unit. -/
theorem contribution_add_cachedAt_le_of_child_settled {cache cache' : QueryCache HashSpec}
    (hle : cache ≤ cache') {parent child : Position} (hmem : child ∈ parent.children)
    (hunsettled : ¬ Settled parameter otsSecret ftsSecret cache child)
    (hsettled : Settled parameter otsSecret ftsSecret cache' child)
    (hcachedAt : cachedAt parameter cache' parent = cachedAt parameter cache parent) :
    contribution parameter otsSecret ftsSecret cache' parent
        + (cachedAt parameter cache parent).ncard
      ≤ contribution parameter otsSecret ftsSecret cache parent := by
  have hparentUnsettled : ¬ Settled parameter otsSecret ftsSecret cache parent := by
    intro hp
    exact hunsettled (hp.children child hmem)
  by_cases hparentSettled : Settled parameter otsSecret ftsSecret cache' parent
  · simp only [contribution, hparentSettled, hparentUnsettled, if_true, if_false, zero_add]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  · simp only [contribution, hparentSettled, hparentUnsettled, if_false, hcachedAt]
    have hdrop := unsettledChildren_ncard_lt parameter otsSecret ftsSecret hle hmem
      hunsettled hsettled
    nlinarith

/-- The units released when a query settles its position pay for all of `settlingTargets`. -/
theorem potential_add_settlingTargets_card_le {cache : QueryCache HashSpec}
    (hfinite : Finite cache) {input₀ : HashInput} {answer : HashOutput} {p₀ : Position}
    (huncached : cache input₀ = none) (hposition : AtPosition parameter input₀ p₀)
    (hunsettled : ¬ Settled parameter otsSecret ftsSecret cache p₀)
    (hsettled : Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p₀) :
    potential parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer)
        + (settlingTargets parameter cache hfinite p₀).card
      ≤ potential parameter otsSecret ftsSecret cache := by
  classical
  let cache' := cache.cacheQuery input₀ answer
  have hle : cache ≤ cache' := le_cacheQuery huncached
  obtain ⟨_, hchildren⟩ := eq_cachedInput_and_children_of_settled_cacheQuery
    parameter otsSecret ftsSecret huncached hposition hunsettled hsettled
  have hrelease₀ : contribution parameter otsSecret ftsSecret cache' p₀
        + (cachedAt parameter cache p₀).ncard
      ≤ contribution parameter otsSecret ftsSecret cache p₀ :=
    contribution_add_cachedAt_le_of_settled parameter otsSecret ftsSecret hunsettled
      hsettled hchildren
  have hcard := settlingTargets_card_le parameter cache hfinite p₀
  cases hparent : p₀.parentOf with
  | none =>
      simp only [hparent] at hcard
      have hsum : ∑ p : Position, (contribution parameter otsSecret ftsSecret cache' p
            + if p = p₀ then (cachedAt parameter cache p₀).ncard else 0)
          ≤ ∑ p : Position, contribution parameter otsSecret ftsSecret cache p := by
        refine Finset.sum_le_sum fun p _ => ?_
        by_cases hp : p = p₀
        · subst hp
          simpa using hrelease₀
        · simp only [hp, if_false, Nat.add_zero]
          have hnotAt : ¬ AtPosition parameter input₀ p := by
            intro hat
            exact hp (atPosition_unique parameter hat hposition)
          exact contribution_le_of_cachedAt_eq parameter otsSecret ftsSecret hle p
            (cachedAt_cacheQuery_of_not_atPosition parameter hnotAt)
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at hsum
      simp only [Finset.mem_univ, if_true] at hsum
      change potential parameter otsSecret ftsSecret cache'
          + (settlingTargets parameter cache hfinite p₀).card
        ≤ potential parameter otsSecret ftsSecret cache
      rw [potential, potential]
      omega
  | some parent =>
      have hmem : p₀ ∈ parent.children := Position.mem_children_iff.mpr hparent
      have hpne : parent ≠ p₀ := by
        intro heq
        subst heq
        have := Position.depth_lt_of_mem_children hmem
        omega
      have hcachedAt : cachedAt parameter cache' parent = cachedAt parameter cache parent :=
        cachedAt_cacheQuery_of_not_atPosition parameter (by
          intro hat
          exact hpne (atPosition_unique parameter hat hposition))
      have hreleaseParent : contribution parameter otsSecret ftsSecret cache' parent
            + (cachedAt parameter cache parent).ncard
          ≤ contribution parameter otsSecret ftsSecret cache parent :=
        contribution_add_cachedAt_le_of_child_settled parameter otsSecret ftsSecret hle hmem
          hunsettled hsettled hcachedAt
      simp only [hparent] at hcard
      have hsum : ∑ p : Position, ((contribution parameter otsSecret ftsSecret cache' p
              + if p = p₀ then (cachedAt parameter cache p₀).ncard else 0)
            + if p = parent then (cachedAt parameter cache parent).ncard else 0)
          ≤ ∑ p : Position, contribution parameter otsSecret ftsSecret cache p := by
        refine Finset.sum_le_sum fun p _ => ?_
        by_cases hq : p = p₀
        · subst hq
          simp only [if_pos, hpne.symm, if_false, Nat.add_zero]
          exact hrelease₀
        · by_cases hp : p = parent
          · subst hp
            simp only [hpne, if_false, if_pos, Nat.add_zero]
            exact hreleaseParent
          · simp only [hq, hp, if_false, Nat.add_zero]
            have hnotAt : ¬ AtPosition parameter input₀ p := by
              intro hat
              exact hq (atPosition_unique parameter hat hposition)
            exact contribution_le_of_cachedAt_eq parameter otsSecret ftsSecret hle p
              (cachedAt_cacheQuery_of_not_atPosition parameter hnotAt)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.sum_ite_eq'] at hsum
      simp only [Finset.mem_univ, if_true] at hsum
      change potential parameter otsSecret ftsSecret cache'
          + (settlingTargets parameter cache hfinite p₀).card
        ≤ potential parameter otsSecret ftsSecret cache
      rw [potential, potential]
      omega

/-- If the queried position remains unsettled, the query deposits at most one slot-vector there. -/
theorem potential_cacheQuery_le_of_unsettled {cache : QueryCache HashSpec} {input₀ : HashInput}
    {answer : HashOutput} {p₀ : Position} (huncached : cache input₀ = none)
    (hposition : AtPosition parameter input₀ p₀)
    (hunsettled : ¬ Settled parameter otsSecret ftsSecret
      (cache.cacheQuery input₀ answer) p₀) :
    potential parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer)
      ≤ potential parameter otsSecret ftsSecret cache + 1 + numChains := by
  classical
  let cache' := cache.cacheQuery input₀ answer
  have hle : cache ≤ cache' := le_cacheQuery huncached
  have hunsettledBefore : ¬ Settled parameter otsSecret ftsSecret cache p₀ := by
    intro hsettled
    exact hunsettled (hsettled.mono hle)
  have hunsettled' : ¬ Settled parameter otsSecret ftsSecret cache' p₀ := by
    simpa [cache'] using hunsettled
  have hcard : (cachedAt parameter cache' p₀).ncard
      ≤ (cachedAt parameter cache p₀).ncard + 1 := by
    rw [show cachedAt parameter cache' p₀
      = insert input₀ (cachedAt parameter cache p₀) from
        cachedAt_cacheQuery_self parameter hposition]
    exact Set.ncard_insert_le _ _
  have hchildren := unsettledChildren_ncard_mono parameter otsSecret ftsSecret hle p₀
  have hp₀ : contribution parameter otsSecret ftsSecret cache' p₀
      ≤ contribution parameter otsSecret ftsSecret cache p₀
        + 1 + (unsettledChildren parameter otsSecret ftsSecret cache p₀).ncard := by
    simp only [contribution, hunsettled', hunsettledBefore, if_false]
    have hmul := Nat.mul_le_mul hcard (Nat.add_le_add_left hchildren 1)
    calc
      _ ≤ ((cachedAt parameter cache p₀).ncard + 1)
          * (1 + (unsettledChildren parameter otsSecret ftsSecret cache p₀).ncard) := hmul
      _ = _ := by ring
  have hwidth := unsettledChildren_ncard_le parameter otsSecret ftsSecret cache p₀
  calc
    potential parameter otsSecret ftsSecret cache'
        = ∑ p : Position, contribution parameter otsSecret ftsSecret cache' p := rfl
    _ ≤ ∑ p : Position, (contribution parameter otsSecret ftsSecret cache p
          + if p = p₀ then 1 +
            (unsettledChildren parameter otsSecret ftsSecret cache p₀).ncard else 0) := by
      refine Finset.sum_le_sum fun p _ => ?_
      by_cases hp : p = p₀
      · subst hp
        simp only [if_pos]
        omega
      · simp only [hp, if_false, Nat.add_zero]
        have hnotAt : ¬ AtPosition parameter input₀ p := by
          intro hat
          exact hp (atPosition_unique parameter hat hposition)
        exact contribution_le_of_cachedAt_eq parameter otsSecret ftsSecret hle p
          (cachedAt_cacheQuery_of_not_atPosition parameter hnotAt)
    _ = potential parameter otsSecret ftsSecret cache + 1
          + (unsettledChildren parameter otsSecret ftsSecret cache p₀).ncard := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp [potential]
      omega
    _ ≤ potential parameter otsSecret ftsSecret cache + 1 + numChains := by omega

/-- If the queried position remains unsettled, no hit can appear. -/
theorem clean_cacheQuery_of_unsettled {cache : QueryCache HashSpec} {input₀ : HashInput}
    {answer : HashOutput} {p₀ : Position}
    (hclean : ¬ Bad parameter otsSecret ftsSecret cache) (huncached : cache input₀ = none)
    (hposition : AtPosition parameter input₀ p₀)
    (hunsettled : ¬ Settled parameter otsSecret ftsSecret
      (cache.cacheQuery input₀ answer) p₀) :
    ¬ Bad parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) := by
  have hle : cache ≤ cache.cacheQuery input₀ answer := le_cacheQuery huncached
  rintro ⟨p, hsettled', input, ax, ay, hat, hne, hinput, hhonest, heq⟩
  have hpne : p ≠ p₀ := fun hp => hunsettled (hp ▸ hsettled')
  have hsettled : Settled parameter otsSecret ftsSecret cache p :=
    settled_of_settled_cacheQuery parameter otsSecret ftsSecret huncached
      (p₀ := some p₀) (fun q hq => by
        rw [atPosition_unique parameter hposition hq]) (by
          intro q parent hq hparent hparentSettled
          rw [Option.some.injEq] at hq
          subst hq
          exact hunsettled (hparentSettled.children p₀ (Position.mem_children_iff.mpr hparent)))
      (p.depth + 1) p (by omega) (by simpa using hpne.symm) hsettled'
  have hpinned := cachedInput_eq_of_settled hle hsettled
  have hinputne : input ≠ input₀ :=
    atPosition_ne parameter hat hposition hpne
  have hhonestne : cachedInput parameter otsSecret ftsSecret cache p ≠ input₀ :=
    atPosition_ne parameter (atPosition_cachedInput parameter otsSecret ftsSecret cache p)
      hposition hpne
  apply hclean
  refine ⟨p, hsettled, input, ax, ay, hat, ?_, ?_, ?_, heq⟩
  · rwa [hpinned] at hne
  · rwa [QueryCache.cacheQuery_of_ne _ _ hinputne] at hinput
  · rw [hpinned, QueryCache.cacheQuery_of_ne _ _ hhonestne] at hhonest
    exact hhonest

/-- Querying another input at a settled position cannot increase the potential. -/
theorem potential_cacheQuery_le_of_settled {cache : QueryCache HashSpec} {input₀ : HashInput}
    {answer : HashOutput} {p₀ : Position} (huncached : cache input₀ = none)
    (hposition : AtPosition parameter input₀ p₀)
    (hsettled : Settled parameter otsSecret ftsSecret cache p₀) :
    potential parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer)
      ≤ potential parameter otsSecret ftsSecret cache := by
  classical
  have hle : cache ≤ cache.cacheQuery input₀ answer := le_cacheQuery huncached
  have hsettled' : Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p₀ :=
    hsettled.mono hle
  rw [potential, potential]
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases hp : p = p₀
  · subst hp
    simp [contribution, hsettled, hsettled']
  · have hnotAt : ¬ AtPosition parameter input₀ p := by
      intro hat
      exact hp (atPosition_unique parameter hat hposition)
    exact contribution_le_of_cachedAt_eq parameter otsSecret ftsSecret hle p
      (cachedAt_cacheQuery_of_not_atPosition parameter hnotAt)

/-- At a settled position the only fresh target is its pinned honest value. -/
theorem clean_cacheQuery_of_settled_of_avoids {cache : QueryCache HashSpec}
    {input₀ : HashInput} {answer : HashOutput} {p₀ : Position}
    (hclean : ¬ Bad parameter otsSecret ftsSecret cache) (huncached : cache input₀ = none)
    (hposition : AtPosition parameter input₀ p₀)
    (hsettled₀ : Settled parameter otsSecret ftsSecret cache p₀)
    (havoid : truncateHash answer ≠
      honestValue (fromCache cache) parameter otsSecret ftsSecret p₀) :
    ¬ Bad parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) := by
  have hle : cache ≤ cache.cacheQuery input₀ answer := le_cacheQuery huncached
  rintro ⟨p, hsettled', input, ax, ay, hat, hne, hinput, hhonest, heq⟩
  have hsettled : Settled parameter otsSecret ftsSecret cache p :=
    settled_of_cacheQuery_at_settled parameter otsSecret ftsSecret huncached hposition hsettled₀
      (p.depth + 1) p (by omega) hsettled'
  have hpinned := cachedInput_eq_of_settled hle hsettled
  have hhonestne : cachedInput parameter otsSecret ftsSecret cache p ≠ input₀ := by
    intro heqInput
    have hcached := hsettled.cached
    rw [heqInput, huncached] at hcached
    simp at hcached
  rw [hpinned, QueryCache.cacheQuery_of_ne _ _ hhonestne] at hhonest
  by_cases hinputeq : input = input₀
  · subst hinputeq
    have hp : p = p₀ := atPosition_unique parameter hat hposition
    subst hp
    rw [QueryCache.cacheQuery_self] at hinput
    have hanswer : answer = ax := Option.some.inj hinput
    apply havoid
    rw [hanswer, heq, honestValue]
    change truncateHash ay = truncateHash
      (fromCache cache (cachedInput parameter otsSecret ftsSecret cache p))
    simp [fromCache, hhonest]
  · have hinputOld : cache input = some ax := by
      rwa [QueryCache.cacheQuery_of_ne _ _ hinputeq] at hinput
    apply hclean
    refine ⟨p, hsettled, input, ax, ay, hat, ?_, hinputOld, hhonest, heq⟩
    rwa [hpinned] at hne

/-- If a query settles its position and avoids the charged answers and parent slots, the cache stays
clean. -/
theorem clean_cacheQuery_of_settling_of_avoids {cache : QueryCache HashSpec}
    (hfinite : Finite cache) {input₀ : HashInput} {answer : HashOutput} {p₀ : Position}
    (hclean : ¬ Bad parameter otsSecret ftsSecret cache) (huncached : cache input₀ = none)
    (hposition : AtPosition parameter input₀ p₀)
    (hunsettled : ¬ Settled parameter otsSecret ftsSecret cache p₀)
    (hsettled : Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p₀)
    (havoid : truncateHash answer ∉ settlingTargets parameter cache hfinite p₀) :
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
    have hmem : p₀ ∈ parent.children := Position.mem_children_iff.mpr hparent
    have hslotAvoid : truncateHash answer ∉ slotTargets parameter cache hfinite p₀ parent := by
      intro hmemTarget
      apply havoid
      simp [settlingTargets, hparent, hmemTarget]
    exact not_settled_parent_of_avoids_slotTargets parameter otsSecret ftsSecret hfinite
      huncached hposition hunsettled hsettled hmem hslotAvoid
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
    rw [settlingTargets]
    split
    · exact htarget
    · exact Finset.mem_union_left _ htarget
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

/-- An input outside every structural domain neither creates a hit nor deposits potential. -/
theorem clean_and_potential_cacheQuery_of_not_atPosition {cache : QueryCache HashSpec}
    {input₀ : HashInput} {answer : HashOutput}
    (hclean : ¬ Bad parameter otsSecret ftsSecret cache) (huncached : cache input₀ = none)
    (hposition : ∀ p, ¬ AtPosition parameter input₀ p) :
    ¬ Bad parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer)
      ∧ potential parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer)
        ≤ potential parameter otsSecret ftsSecret cache := by
  classical
  have hle : cache ≤ cache.cacheQuery input₀ answer := le_cacheQuery huncached
  have hpotential : potential parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer)
      ≤ potential parameter otsSecret ftsSecret cache := by
    rw [potential, potential]
    exact Finset.sum_le_sum fun p _ =>
      contribution_le_of_cachedAt_eq parameter otsSecret ftsSecret hle p
        (cachedAt_cacheQuery_of_not_atPosition parameter (hposition p))
  refine ⟨?_, hpotential⟩
  rintro ⟨p, hsettled', input, ax, ay, hat, hne, hinput, hhonest, heq⟩
  have hsettled : Settled parameter otsSecret ftsSecret cache p :=
    settled_of_settled_cacheQuery parameter otsSecret ftsSecret huncached
      (p₀ := none) (fun q hq => absurd hq (hposition q)) (by simp)
      (p.depth + 1) p (by omega) (by simp) hsettled'
  have hpinned := cachedInput_eq_of_settled hle hsettled
  have hinputne : input ≠ input₀ := by
    intro heqInput
    exact hposition p (heqInput ▸ hat)
  have hhonestne : cachedInput parameter otsSecret ftsSecret cache p ≠ input₀ := by
    intro heqInput
    exact hposition p (heqInput ▸ atPosition_cachedInput parameter otsSecret ftsSecret cache p)
  apply hclean
  refine ⟨p, hsettled, input, ax, ay, hat, ?_, ?_, ?_, heq⟩
  · rwa [hpinned] at hne
  · rwa [QueryCache.cacheQuery_of_ne _ _ hinputne] at hinput
  · rw [hpinned, QueryCache.cacheQuery_of_ne _ _ hhonestne] at hhonest
    exact hhonest

end SphincsSecurity

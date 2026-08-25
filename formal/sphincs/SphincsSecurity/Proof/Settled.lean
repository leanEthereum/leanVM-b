import SphincsSecurity.Proof.Honest

/-!
# Positions the cache has settled

A position is *settled* by a cache when every position below it is and the honest input there is
cached. The point of the notion is `honestInput_eq_of_settled`: at a settled position the honest
input is a function of the cache alone, the same for every answer function the cache agrees with. It
is what lets the accounting speak of "the honest input at this domain" without knowing the rest of
the run, and what the extraction's honest values are matched against.

Settling is monotone, and the input it pins never moves again.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

/-- The answer function a cache induces: its own answers, and `0` where it says nothing. -/
def fromCache (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD 0

theorem agreesWithFn_fromCache (cache : QueryCache HashSpec) :
    cache.AgreesWithFn (fromCache cache) := by
  intro input answer hcached
  simp [fromCache, hcached]

theorem agreesWithFn_fromCache_of_le {cache cache' : QueryCache HashSpec} (hle : cache ≤ cache') :
    cache.AgreesWithFn (fromCache cache') := fun _ _ hcached => by
  simp [fromCache, hle hcached]

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

/-- The honest input at a position, as the cache pins it. -/
noncomputable def cachedInput (cache : QueryCache HashSpec) (p : Position) : HashInput :=
  honestInput (fromCache cache) parameter otsSecret ftsSecret p

/-- Every position below this one is settled, and the honest input here is cached. -/
def Settled (cache : QueryCache HashSpec) (p : Position) : Prop :=
  p.Valid ∧ cache (cachedInput parameter otsSecret ftsSecret cache p) ≠ none
    ∧ ∀ c ∈ p.children, Settled cache c
termination_by p.depth
decreasing_by exact Position.depth_lt_of_mem_children (by assumption)

theorem settled_iff (cache : QueryCache HashSpec) (p : Position) :
    Settled parameter otsSecret ftsSecret cache p
      ↔ p.Valid ∧ cache (cachedInput parameter otsSecret ftsSecret cache p) ≠ none
        ∧ ∀ c ∈ p.children, Settled parameter otsSecret ftsSecret cache c := by
  rw [Settled]

variable {parameter} {otsSecret} {ftsSecret}

theorem Settled.valid {cache : QueryCache HashSpec} {p : Position}
    (h : Settled parameter otsSecret ftsSecret cache p) : p.Valid :=
  ((settled_iff parameter otsSecret ftsSecret cache p).mp h).1

theorem Settled.cached {cache : QueryCache HashSpec} {p : Position}
    (h : Settled parameter otsSecret ftsSecret cache p) :
    cache (cachedInput parameter otsSecret ftsSecret cache p) ≠ none :=
  ((settled_iff parameter otsSecret ftsSecret cache p).mp h).2.1

theorem Settled.children {cache : QueryCache HashSpec} {p : Position}
    (h : Settled parameter otsSecret ftsSecret cache p) :
    ∀ c ∈ p.children, Settled parameter otsSecret ftsSecret cache c :=
  ((settled_iff parameter otsSecret ftsSecret cache p).mp h).2.2

/-- **A settled position is pinned.** At a settled position every answer function the cache agrees
with gives the same honest input, and the same honest value. -/
private theorem honestInput_eq_of_settled_aux {cache : QueryCache HashSpec}
    {f : QueryImpl HashSpec Id} (hf : cache.AgreesWithFn f) :
    ∀ (n : Nat) (p : Position), p.depth < n → Settled parameter otsSecret ftsSecret cache p →
      honestInput f parameter otsSecret ftsSecret p
          = cachedInput parameter otsSecret ftsSecret cache p
        ∧ honestValue f parameter otsSecret ftsSecret p
          = honestValue (fromCache cache) parameter otsSecret ftsSecret p := by
  intro n
  induction n with
  | zero => intro p hdepth; omega
  | succ n ih =>
      intro p hdepth hsettled
      have hchildren : ∀ c ∈ p.children,
          honestValue f parameter otsSecret ftsSecret c
            = honestValue (fromCache cache) parameter otsSecret ftsSecret c := fun c hc =>
        (ih c (by have := Position.depth_lt_of_mem_children hc; omega)
          (hsettled.children c hc)).2
      have hinput := honestInput_congr f (fromCache cache) parameter otsSecret ftsSecret
        hsettled.valid hchildren
      refine ⟨hinput, ?_⟩
      obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hsettled.cached
      rw [honestValue, honestValue, hinput]
      change truncateHash (f (cachedInput parameter otsSecret ftsSecret cache p))
        = truncateHash (fromCache cache (cachedInput parameter otsSecret ftsSecret cache p))
      rw [hf hanswer, show fromCache cache (cachedInput parameter otsSecret ftsSecret cache p)
        = answer from by simp [fromCache, hanswer]]

theorem honestInput_eq_cachedInput {cache : QueryCache HashSpec} {f : QueryImpl HashSpec Id}
    (hf : cache.AgreesWithFn f) {p : Position}
    (hsettled : Settled parameter otsSecret ftsSecret cache p) :
    honestInput f parameter otsSecret ftsSecret p
      = cachedInput parameter otsSecret ftsSecret cache p :=
  (honestInput_eq_of_settled_aux hf (p.depth + 1) p (by omega) hsettled).1

theorem honestValue_eq_of_settled {cache : QueryCache HashSpec} {f : QueryImpl HashSpec Id}
    (hf : cache.AgreesWithFn f) {p : Position}
    (hsettled : Settled parameter otsSecret ftsSecret cache p) :
    honestValue f parameter otsSecret ftsSecret p
      = honestValue (fromCache cache) parameter otsSecret ftsSecret p :=
  (honestInput_eq_of_settled_aux hf (p.depth + 1) p (by omega) hsettled).2

/-- A valid position settles once its children are settled and its honest input is cached. -/
theorem settled_of_honestInput_cached {cache : QueryCache HashSpec}
    {f : QueryImpl HashSpec Id} (hf : cache.AgreesWithFn f) {p : Position}
    (hvalid : p.Valid)
    (hcached : cache (honestInput f parameter otsSecret ftsSecret p) ≠ none)
    (hchildren : ∀ c ∈ p.children, Settled parameter otsSecret ftsSecret cache c) :
    Settled parameter otsSecret ftsSecret cache p := by
  have hvalues : ∀ c ∈ p.children,
      honestValue f parameter otsSecret ftsSecret c
        = honestValue (fromCache cache) parameter otsSecret ftsSecret c := fun c hc =>
    honestValue_eq_of_settled hf (hchildren c hc)
  have hinput := honestInput_congr f (fromCache cache) parameter otsSecret ftsSecret hvalid hvalues
  rw [settled_iff]
  refine ⟨hvalid, ?_, hchildren⟩
  change cache (honestInput (fromCache cache) parameter otsSecret ftsSecret p) ≠ none
  rwa [← hinput]

/-- **Settling is monotone, and what it pins does not move.** -/
private theorem settled_mono_aux {cache cache' : QueryCache HashSpec} (hle : cache ≤ cache') :
    ∀ (n : Nat) (p : Position), p.depth < n → Settled parameter otsSecret ftsSecret cache p →
      Settled parameter otsSecret ftsSecret cache' p
        ∧ cachedInput parameter otsSecret ftsSecret cache' p
          = cachedInput parameter otsSecret ftsSecret cache p := by
  intro n
  induction n with
  | zero => intro p hdepth; omega
  | succ n ih =>
      intro p hdepth hsettled
      have hpinned : cachedInput parameter otsSecret ftsSecret cache' p
          = cachedInput parameter otsSecret ftsSecret cache p :=
        honestInput_eq_cachedInput (agreesWithFn_fromCache_of_le hle) hsettled
      refine ⟨?_, hpinned⟩
      rw [settled_iff]
      refine ⟨hsettled.valid, ?_, fun c hc =>
        (ih c (by have := Position.depth_lt_of_mem_children hc; omega)
          (hsettled.children c hc)).1⟩
      rw [hpinned]
      obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hsettled.cached
      rw [hle hanswer]
      simp

theorem Settled.mono {cache cache' : QueryCache HashSpec} (hle : cache ≤ cache') {p : Position}
    (h : Settled parameter otsSecret ftsSecret cache p) :
    Settled parameter otsSecret ftsSecret cache' p :=
  (settled_mono_aux hle (p.depth + 1) p (by omega) h).1

theorem cachedInput_eq_of_settled {cache cache' : QueryCache HashSpec} (hle : cache ≤ cache')
    {p : Position} (h : Settled parameter otsSecret ftsSecret cache p) :
    cachedInput parameter otsSecret ftsSecret cache' p
      = cachedInput parameter otsSecret ftsSecret cache p :=
  (settled_mono_aux hle (p.depth + 1) p (by omega) h).2

end SphincsSecurity

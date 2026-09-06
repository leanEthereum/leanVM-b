import SphincsSecurity.Proof.Descent

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

noncomputable def retainHonestCache (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (inputs : Set HashInput) : QueryCache HashSpec :=
  open Classical in
  fun input => if input ∈ inputs ∨ ∃ position,
    Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position ∧
      input = cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position
    then cache input else none

theorem retainHonestCache_le (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (inputs : Set HashInput) :
    retainHonestCache secretKey cache inputs ≤ cache := by
  intro input answer hcached
  unfold retainHonestCache at hcached
  split_ifs at hcached
  exact hcached

theorem retainHonestCache_agreesWithFn (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (inputs : Set HashInput)
    (f : QueryImpl HashSpec Id) (hf : cache.AgreesWithFn f) :
    (retainHonestCache secretKey cache inputs).AgreesWithFn f :=
  fun _ _ hcached => hf (retainHonestCache_le secretKey cache inputs hcached)

theorem settled_retainHonestCache (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (inputs : Set HashInput) (position : Position)
    (hsettled : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position) :
    Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (retainHonestCache secretKey cache inputs) position := by
  have hf := retainHonestCache_agreesWithFn secretKey cache inputs (fromCache cache)
    (agreesWithFn_fromCache cache)
  suffices ∀ n p, p.depth < n →
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache p →
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        (retainHonestCache secretKey cache inputs) p from
    this (position.depth + 1) position (by omega) hsettled
  intro n
  induction n with
  | zero => intro p hdepth; omega
  | succ n ih =>
      intro p hdepth hp
      apply settled_of_honestInput_cached hf hp.valid
      · change retainHonestCache secretKey cache inputs
          (cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache p) ≠ none
        have hkeep : ∃ position,
            Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position ∧
              cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache p =
                cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position :=
          ⟨p, hp, rfl⟩
        simpa only [retainHonestCache, hkeep, or_true, if_true] using hp.cached
      · intro child hchild
        apply ih child _ (hp.children child hchild)
        have := Position.depth_lt_of_mem_children hchild
        omega

theorem cachedRun_retainHonestCache (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (inputs : Set HashInput)
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α)
    (hrun : CachedRun cache f computation)
    (hinputs : ∀ input ∈ queriedInputs f computation, input ∈ inputs) :
    CachedRun (retainHonestCache secretKey cache inputs) f computation := by
  intro input hinput
  simpa only [retainHonestCache, hinputs input hinput, true_or, if_true] using hrun input hinput

def BadOnInputs (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (inputs : Set HashInput) : Prop :=
  ∃ position input ax ay,
    input ∈ inputs ∧
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position ∧
      AtPosition secretKey.parameter input position ∧
      input ≠ cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position ∧
      cache input = some ax ∧
      cache (cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position) = some ay ∧
      truncateHash ax = truncateHash ay

theorem BadOnInputs.bad {secretKey : SecretKey} {cache : QueryCache HashSpec}
    {inputs : Set HashInput} (hbad : BadOnInputs secretKey cache inputs) :
    Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache := by
  obtain ⟨position, input, ax, ay, _, hsettled, hat, hne, hx, hy, heq⟩ := hbad
  exact ⟨position, hsettled, input, ax, ay, hat, hne, hx, hy, heq⟩

theorem BadOnInputs.mono_inputs {secretKey : SecretKey} {cache : QueryCache HashSpec}
    {inputs more : Set HashInput} (hsub : inputs ⊆ more)
    (hbad : BadOnInputs secretKey cache inputs) : BadOnInputs secretKey cache more := by
  obtain ⟨position, input, ax, ay, hinput, hrest⟩ := hbad
  exact ⟨position, input, ax, ay, hsub hinput, hrest⟩

theorem bad_retainHonestCache_iff (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (inputs : Set HashInput) :
    Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (retainHonestCache secretKey cache inputs) ↔ BadOnInputs secretKey cache inputs := by
  classical
  let restricted := retainHonestCache secretKey cache inputs
  have hle : restricted ≤ cache := retainHonestCache_le secretKey cache inputs
  constructor
  · rintro ⟨position, hsettled, input, ax, ay, hat, hne, hx, hy, heq⟩
    have hpinned := cachedInput_eq_of_settled hle hsettled
    have hne' : input ≠ cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position := by
      rwa [hpinned]
    have hinput : input ∈ inputs := by
      by_contra hnot
      have hkeep : ∃ other,
          Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache other ∧
            input = cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache other := by
        by_contra hnone
        simp only [retainHonestCache, hnot, hnone, or_self, if_false] at hx
        simp at hx
      obtain ⟨other, _, hother⟩ := hkeep
      have hatOther : AtPosition secretKey.parameter input other := by
        rw [hother]
        exact atPosition_cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache other
      have hpositions := atPosition_unique secretKey.parameter hat hatOther
      exact hne' (hother.trans (congrArg _ hpositions.symm))
    exact ⟨position, input, ax, ay, hinput, hsettled.mono hle, hat, hne', hle hx,
      by rw [hpinned]; exact hle hy, heq⟩
  · rintro ⟨position, input, ax, ay, hinput, hsettled, hat, hne, hx, hy, heq⟩
    have hsettled' := settled_retainHonestCache secretKey cache inputs position hsettled
    have hpinned := cachedInput_eq_of_settled hle hsettled'
    refine ⟨position, hsettled', input, ax, ay, hat, ?_, ?_, ?_, heq⟩
    · rwa [← hpinned]
    · simpa only [retainHonestCache, hinput, true_or, if_true] using hx
    · rw [← hpinned]
      have hkeep : ∃ other,
          Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache other ∧
            cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position =
              cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache other :=
        ⟨position, hsettled, rfl⟩
      simpa only [retainHonestCache, hkeep, or_true, if_true] using hy

end SphincsSecurity.Concrete

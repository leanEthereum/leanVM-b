import SphincsSecurity.Proof.FewTimeNumberedSources

/-!
# Reusing one fixed cached message entry

Once an origin configuration fixes a direct source, the later signer has to select that source's
one exact message-digest input. Restricting the reference cache to this input turns the cached-entry
factor in the digest race into one.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

def onlyInputCache (cache : QueryCache HashSpec) (target : HashInput) :
    QueryCache HashSpec :=
  fun input => if input = target then cache input else none

theorem onlyInputCache_le (cache : QueryCache HashSpec) (target : HashInput) :
    onlyInputCache cache target ≤ cache := by
  intro input output hcached
  by_cases hinput : input = target
  · simpa [onlyInputCache, hinput] using hcached
  · simp [onlyInputCache, hinput] at hcached

theorem cachedMessageEntryCountWhere_onlyInput_le_one
    (cache : QueryCache HashSpec) (target : HashInput)
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (P : Concrete.FewTimeView → Prop) :
    cachedMessageEntryCountWhere (onlyInputCache cache target) parameter root message P ≤ 1 := by
  have hsubsingleton :
      (cachedMessageInputSetWhere (onlyInputCache cache target) parameter root message P).Subsingleton := by
    rintro ⟨leftInput, leftOutput⟩ hleft ⟨rightInput, rightOutput⟩ hright
    have hleftInput : leftInput = target := by
      by_contra hne
      simp [cachedMessageInputSetWhere, cachedMessageInputSet, onlyInputCache, hne]
        at hleft
    have hrightInput : rightInput = target := by
      by_contra hne
      simp [cachedMessageInputSetWhere, cachedMessageInputSet, onlyInputCache, hne]
        at hright
    subst leftInput
    subst rightInput
    have houtputs : leftOutput = rightOutput := by
      apply Option.some.inj
      exact hleft.1.1.symm.trans hright.1.1
    subst rightOutput
    rfl
  have hencard :
      (cachedMessageInputSetWhere (onlyInputCache cache target) parameter root message P).encard ≤ 1 :=
    Set.encard_le_one_iff_subsingleton.2 hsubsingleton
  simpa only [cachedMessageEntryCountWhere, ENat.toENNReal_one] using
    ENat.toENNReal_mono hencard

theorem Concrete.probEvent_signWithView_fixedPrehit_le_race
    (secretKey : SecretKey) (message : Message) (initialCache : QueryCache HashSpec)
    (target : HashInput) (P : FewTimeView → Prop)
    (hbudget : QueryCache.enncard initialCache + (digestAttemptLimit : ℝ≥0∞) ≤
      ((2 ^ 127 : Nat) : ℝ≥0∞)) :
    Pr[PrehitSuccessfulSignerView (onlyInputCache initialCache target) secretKey message P |
      (simulateQ romImpl (signWithView secretKey message)).run initialCache] ≤
      ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    Pr[PrehitSuccessfulSignerView (onlyInputCache initialCache target) secretKey message P |
        (simulateQ romImpl (signWithView secretKey message)).run initialCache] ≤
        cachedMessageEntryCountWhere (onlyInputCache initialCache target)
          secretKey.parameter secretKey.root message P *
            ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ :=
      probEvent_signWithView_prehitSuccessful_le_race_reference secretKey message
        (onlyInputCache initialCache target) initialCache P
        (onlyInputCache_le initialCache target) hbudget
    _ ≤ 1 * ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ := by
      gcongr
      exact cachedMessageEntryCountWhere_onlyInput_le_one initialCache target
        secretKey.parameter secretKey.root message P
    _ = _ := one_mul _

theorem Concrete.probEvent_signWithView_fixedPrehit_le_race_of_enncard_le
    (secretKey : SecretKey) (message : Message) (initialCache : QueryCache HashSpec)
    (target : HashInput) (P : FewTimeView → Prop)
    (q : Nat) (hq : q ≤ 2 ^ 125) (hcache : QueryCache.enncard initialCache ≤ q) :
    Pr[PrehitSuccessfulSignerView (onlyInputCache initialCache target) secretKey message P |
      (simulateQ romImpl (signWithView secretKey message)).run initialCache] ≤
      ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ := by
  apply probEvent_signWithView_fixedPrehit_le_race
  have hq' : (q : ℝ≥0∞) ≤ ((2 ^ 125 : Nat) : ℝ≥0∞) := by
    exact_mod_cast hq
  calc
    QueryCache.enncard initialCache + (digestAttemptLimit : ℝ≥0∞) ≤
        (q : ℝ≥0∞) + (digestAttemptLimit : ℝ≥0∞) :=
      add_le_add hcache le_rfl
    _ ≤ ((2 ^ 125 : Nat) : ℝ≥0∞) + (digestAttemptLimit : ℝ≥0∞) :=
      add_le_add hq' le_rfl
    _ ≤ ((2 ^ 127 : Nat) : ℝ≥0∞) := by
      norm_num [digestAttemptLimit]

end SphincsSecurity

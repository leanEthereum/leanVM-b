import SphincsSecurity.Proof.RetainedCollisionCache
import SphincsSecurity.Proof.Guess
import SphincsSecurity.Proof.RomQueryCharge

namespace SphincsSecurity.Concrete.SettledCollision

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

def SettledInput (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : HashInput) : Prop :=
  ∃ position, AtPosition secretKey.parameter input position ∧
    Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position

def Collision (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : HashInput) (answer : HashOutput) : Prop :=
  cache input = none ∧ ∃ position,
    AtPosition secretKey.parameter input position ∧
    Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position ∧
    truncateHash answer =
      honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret secretKey.ftsSecret position

noncomputable def queryCharge (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : HashInput) : ℝ≥0∞ :=
  if cache input = none ∧ SettledInput secretKey cache input then 1 else 0

theorem queryCharge_le_one (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : HashInput) : queryCharge secretKey cache input ≤ 1 := by
  unfold queryCharge
  split_ifs <;> simp

theorem probEvent_collision_le_charge (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : HashInput) :
    Pr[Collision secretKey cache input | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      queryCharge secretKey cache input * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  by_cases heligible : cache input = none ∧ SettledInput secretKey cache input
  · obtain ⟨hfresh, position, hat, hsettled⟩ := heligible
    rw [queryCharge, if_pos ⟨hfresh, position, hat, hsettled⟩, one_mul]
    calc
      _ ≤ Pr[fun answer => truncateHash answer =
          honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret secretKey.ftsSecret position |
            ($ᵗ HashOutput : ProbComp HashOutput)] := by
        apply probEvent_mono
        rintro answer _ ⟨_, other, hother, _, hvalue⟩
        rwa [atPosition_unique secretKey.parameter hother hat] at hvalue
      _ ≤ _ := by
        rw [← probOutput_map]
        simpa using probOutput_truncateHash_le
          (honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret secretKey.ftsSecret position)
  · have hempty : ∀ answer, ¬ Collision secretKey cache input answer := by
      rintro answer ⟨hfresh, position, hat, hsettled, _⟩
      exact heligible ⟨hfresh, position, hat, hsettled⟩
    simp [queryCharge, heligible, probEvent_eq_tsum_ite, hempty]

theorem collision_bad_cacheQuery {secretKey : SecretKey} {cache : QueryCache HashSpec}
    {input : HashInput} {answer : HashOutput}
    (hcollision : Collision secretKey cache input answer) :
    BadOnInputs secretKey (cache.cacheQuery input answer) {input} := by
  obtain ⟨hfresh, position, hat, hsettled, hvalue⟩ := hcollision
  have hle := le_cacheQuery (answer := answer) hfresh
  have hpinned := cachedInput_eq_of_settled hle hsettled
  have hne : input ≠ cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position := by
    intro heq
    exact hsettled.cached (heq ▸ hfresh)
  obtain ⟨honestAnswer, hhonest⟩ := Option.ne_none_iff_exists'.mp hsettled.cached
  refine ⟨position, input, answer, honestAnswer, rfl, hsettled.mono hle, hat, ?_,
    QueryCache.cacheQuery_self _ _ _, ?_, ?_⟩
  · rwa [hpinned]
  · rw [hpinned]
    exact hle hhonest
  · change truncateHash answer = truncateHash
      (fromCache cache (cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position)) at hvalue
    simpa only [fromCache, hhonest, Option.getD_some] using hvalue

end SphincsSecurity.Concrete.SettledCollision

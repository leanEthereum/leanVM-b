import SphincsSecurity.Proof.WorldRawIndexEnvelope
import SphincsSecurity.Proof.CacheSlotCount

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)

def cachedMessageInputs (parameter : PublicParameter) (cache : QueryCache HashSpec) : Set HashInput :=
  {input | cache input ≠ none ∧ MessageHashInput parameter input}

noncomputable def messageCacheSlotCount (parameter : PublicParameter) (q : Nat) (cache : QueryCache HashSpec) : Nat :=
  q - (cachedMessageInputs parameter cache).ncard

theorem cachedMessageInputs_finite (parameter : PublicParameter) (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (cachedMessageInputs parameter cache).Finite :=
  hfinite.subset (fun _ h => h.1)

theorem cachedMessageInputs_mono (parameter : PublicParameter) (before after : QueryCache HashSpec) (hle : before ≤ after) :
    cachedMessageInputs parameter before ⊆ cachedMessageInputs parameter after := by
  intro input h
  obtain ⟨answer, ha⟩ := Option.ne_none_iff_exists'.mp h.1
  exact ⟨Option.ne_none_iff_exists'.mpr ⟨answer, hle ha⟩, h.2⟩

theorem cachedMessageInputs_cacheQuery_message (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : HashInput) (output : HashOutput) (hmessage : MessageHashInput parameter input) :
    cachedMessageInputs parameter (cache.cacheQuery input output) = insert input (cachedMessageInputs parameter cache) := by
  ext other
  by_cases heq : other = input
  · subst other
    simp [cachedMessageInputs, hmessage]
  · simp only [cachedMessageInputs, Set.mem_setOf_eq, QueryCache.cacheQuery_of_ne _ _ heq,
      Set.mem_insert_iff, heq, false_or]

theorem cachedMessageInputs_cacheQuery_nonmessage (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : HashInput) (output : HashOutput) (hmessage : ¬ MessageHashInput parameter input) :
    cachedMessageInputs parameter (cache.cacheQuery input output) = cachedMessageInputs parameter cache := by
  ext other
  by_cases heq : other = input
  · subst other
    simp [cachedMessageInputs, hmessage]
  · simp only [cachedMessageInputs, Set.mem_setOf_eq, QueryCache.cacheQuery_of_ne _ _ heq]

theorem messageCacheSlotCount_cacheQuery_nonmessage (parameter : PublicParameter) (q : Nat) (cache : QueryCache HashSpec)
    (input : HashInput) (output : HashOutput) (hmessage : ¬ MessageHashInput parameter input) :
    messageCacheSlotCount parameter q (cache.cacheQuery input output) = messageCacheSlotCount parameter q cache := by
  rw [messageCacheSlotCount, cachedMessageInputs_cacheQuery_nonmessage parameter cache input output hmessage]
  rfl

theorem messageCacheSlotCount_antitone (parameter : PublicParameter) (q : Nat) (before after : QueryCache HashSpec)
    (hle : before ≤ after) (hfinite : Finite after) :
    messageCacheSlotCount parameter q after ≤ messageCacheSlotCount parameter q before :=
  Nat.sub_le_sub_left (Set.ncard_le_ncard (cachedMessageInputs_mono parameter before after hle)
    (cachedMessageInputs_finite parameter after hfinite)) q

theorem cachedMessageInputs_ncard_le (parameter : PublicParameter) (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (cachedMessageInputs parameter cache).ncard ≤ {input | cache input ≠ none}.ncard :=
  Set.ncard_le_ncard (fun _ h => h.1) hfinite

theorem cacheSlotCount_le_message (parameter : PublicParameter) (q : Nat) (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    cacheSlotCount q cache ≤ messageCacheSlotCount parameter q cache :=
  Nat.sub_le_sub_left (cachedMessageInputs_ncard_le parameter cache hfinite) q

theorem messageCacheSlotCount_cacheQuery_succ (parameter : PublicParameter) (q : Nat) (cache : QueryCache HashSpec)
    (input : HashInput) (output : HashOutput) (hfresh : cache input = none)
    (hmessage : MessageHashInput parameter input) (hcap : QueryCache.enncard cache + 1 ≤ q) :
    messageCacheSlotCount parameter q cache = messageCacheSlotCount parameter q (cache.cacheQuery input output) + 1 := by
  have hfinite := Finite.of_enncard_le (le_self_add.trans hcap)
  have hcount : {other | cache other ≠ none}.ncard + 1 ≤ q := by
    rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard] at hcap
    exact_mod_cast hcap
  have hle := cachedMessageInputs_ncard_le parameter cache hfinite
  have hnot : input ∉ cachedMessageInputs parameter cache := fun h => h.1 hfresh
  simp only [messageCacheSlotCount, cachedMessageInputs_cacheQuery_message parameter cache input output hmessage,
    Set.ncard_insert_of_notMem hnot (cachedMessageInputs_finite parameter cache hfinite)]
  omega

theorem messageCacheSlotCount_initial (parameter : PublicParameter) (q : Nat) (cache : QueryCache HashSpec)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none) :
    messageCacheSlotCount parameter q cache = q := by
  have hempty : cachedMessageInputs parameter cache = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro input h
    exact h.1 (hnone input h.2)
  simp [messageCacheSlotCount, hempty]

end SphincsSecurity.Concrete

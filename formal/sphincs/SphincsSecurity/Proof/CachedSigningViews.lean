import SphincsSecurity.Proof.ObservedSignerCoverStep

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def SigningCacheCovered (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) : Prop :=
  CoveredMessageCache parameter (fixedSigningViews parameter cache root log) cache

theorem SigningDigestsCached.mono {parameter : PublicParameter} {root : Digest}
    {before after : QueryCache HashSpec} {log : QueryLog SigningSpec}
    (hsigned : SigningDigestsCached parameter before root log) (hcache : before ≤ after) :
    SigningDigestsCached parameter after root log := by
  intro entry hentry signature hresponse
  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (hsigned entry hentry signature hresponse)
  exact Option.ne_none_iff_exists'.mpr ⟨output, hcache houtput⟩

theorem eligibleSigningView?_cache_stable (parameter : PublicParameter) (root : Digest)
    (before after : QueryCache HashSpec) (hcache : before ≤ after) (payload : HashInput) (entry : SigningEntry)
    (hsigned : ∀ signature, entry.2 = some signature →
      messageAnswers parameter before (messageDigestPayload root entry.1 signature.randomness) ≠ none) :
    eligibleSigningView? (messageAnswers parameter after) root payload entry =
      eligibleSigningView? (messageAnswers parameter before) root payload entry := by
  cases hresponse : entry.2 with
  | none => simp [eligibleSigningView?, hresponse]
  | some signature =>
      obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (hsigned signature hresponse)
      have hafter : messageAnswers parameter after (messageDigestPayload root entry.1 signature.randomness) = some output := hcache houtput
      simp [eligibleSigningView?, observedSigningView?, hresponse, houtput, hafter]

theorem fixedSigningViews_cache_stable (parameter : PublicParameter) (root : Digest)
    (before after : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached parameter before root log) :
    fixedSigningViews parameter after root log = fixedSigningViews parameter before root log := by
  funext input slot
  exact eligibleSigningView?_cache_stable parameter root before after hcache (payloadOf input) (log.get slot)
    (hsigned _ (List.get_mem _ _))

theorem covered_eligibleSigningViews_iff (answers : HashInput → Option HashOutput) (root : Digest)
    (payload : HashInput) (log : QueryLog SigningSpec) (target : FewTimeView) :
    CoveredFewTimeView (eligibleSigningViews answers root payload log) target ↔
      ∀ tree, ∃ entry ∈ log, ∃ view, eligibleSigningView? answers root payload entry = some view ∧
        view.1 = target.1 ∧ view.2 tree = target.2 tree := by
  constructor
  · intro hcover tree
    obtain ⟨slot, view, hview, hindex, hleaf⟩ := hcover tree
    exact ⟨log.get slot, List.get_mem _ _, view, hview, hindex, hleaf⟩
  · intro hcover tree
    obtain ⟨entry, hentry, view, hview, hindex, hleaf⟩ := hcover tree
    obtain ⟨slot, hslot⟩ := List.mem_iff_get.mp hentry
    exact ⟨slot, view, by simpa only [eligibleSigningViews, hslot] using hview, hindex, hleaf⟩

theorem covered_eligibleSigningViews_append_none (answers : HashInput → Option HashOutput) (root : Digest)
    (payload : HashInput) (log : QueryLog SigningSpec) (entry : SigningEntry) (target : FewTimeView)
    (hnone : eligibleSigningView? answers root payload entry = none)
    (hcover : CoveredFewTimeView (eligibleSigningViews answers root payload (log ++ [entry])) target) :
    CoveredFewTimeView (eligibleSigningViews answers root payload log) target := by
  rw [covered_eligibleSigningViews_iff] at hcover ⊢
  intro tree
  obtain ⟨selected, hselected, view, hview, hindex, hleaf⟩ := hcover tree
  rcases List.mem_append.mp hselected with hold | hnew
  · exact ⟨selected, hold, view, hview, hindex, hleaf⟩
  · obtain rfl := List.mem_singleton.mp hnew
    rw [hnone] at hview
    simp only [reduceCtorEq] at hview

theorem covered_eligibleSigningViews_append_some (answers : HashInput → Option HashOutput) (root : Digest)
    (payload : HashInput) (log : QueryLog SigningSpec) (entry : SigningEntry) (source target : FewTimeView)
    (hsome : eligibleSigningView? answers root payload entry = some source)
    (hcover : CoveredFewTimeView (eligibleSigningViews answers root payload (log ++ [entry])) target) :
    CoveredFewTimeView (insertFewTimeView (eligibleSigningViews answers root payload log) source) target := by
  rw [covered_eligibleSigningViews_iff] at hcover
  intro tree
  obtain ⟨selected, hselected, view, hview, hindex, hleaf⟩ := hcover tree
  rcases List.mem_append.mp hselected with hold | hnew
  · obtain ⟨slot, hslot⟩ := List.mem_iff_get.mp hold
    refine ⟨slot.succ, view, ?_, hindex, hleaf⟩
    simpa only [insertFewTimeView, Fin.cons_succ, eligibleSigningViews, hslot] using hview
  · obtain rfl := List.mem_singleton.mp hnew
    have heq : source = view := Option.some.inj (hsome.symm.trans hview)
    exact ⟨0, source, rfl, heq ▸ hindex, heq ▸ hleaf⟩

theorem SigningDigestsCached.after_signing (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (response : Option Signature) (view : Option FewTimeView)
    (hresult : ((response, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    SigningDigestsCached key.parameter after key.root (log ++ [⟨message, response⟩]) := by
  have hcache := simulateQ_romImpl_cache_le (signWithView key message) before ((response, view), after) hresult
  intro entry hentry signature hresponse
  rcases List.mem_append.mp hentry with hold | hnew
  · exact (hsigned.mono hcache) entry hold signature hresponse
  · obtain rfl := List.mem_singleton.mp hnew
    have hresponse' : response = some signature := hresponse
    rw [hresponse'] at hresult
    obtain ⟨output, houtput, _, _⟩ := signWithView_successful_cached_output key message before after signature view hresult
    exact Option.ne_none_iff_exists'.mpr ⟨output, houtput⟩

end SphincsSecurity.Concrete

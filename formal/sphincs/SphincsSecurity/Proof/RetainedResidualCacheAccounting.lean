import SphincsSecurity.Proof.RetainedResidualAccounting
import SphincsSecurity.Proof.CertificateCachePersistence

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting ResidualByteAction
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
  signDigestLoop signAfterDigest
set_option backward.isDefEq.respectTransparency false

def CacheSizeBound (memory : Memory) : Prop :=
  QueryCache.enncard memory.external.cache ≤ (memory.external.hashCalls : ENNReal)

private theorem cacheFold_size (entries : List (HashInput × HashOutput)) (cache : ExternalCache) :
    QueryCache.enncard (entries.foldl (fun (current : ExternalCache) entry => Function.update current entry.1 (some entry.2)) cache) ≤
      QueryCache.enncard cache + (entries.length : ENNReal) := by
  induction entries generalizing cache with
  | nil => simp only [List.foldl_nil, List.length_nil, Nat.cast_zero, add_zero, le_refl]
  | cons entry entries ih =>
      refine (ih (Function.update cache entry.1 (some entry.2))).trans ?_
      calc
        _ ≤ (QueryCache.enncard cache + 1) + (entries.length : ENNReal) :=
          add_le_add (QueryCache.enncard_cacheQuery_le cache entry.1 entry.2) le_rfl
        _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ac_rfl

theorem CacheSizeBound.applyBoundary {memory : Memory} (hbound : CacheSizeBound memory) (trace : SigningBoundaryTrace) :
    CacheSizeBound (memory.applyBoundary trace) := by
  have hlength : (trace.messageCalls.length : ENNReal) ≤ trace.hashCalls := Nat.cast_le.mpr (List.length_filterMap_le _ _)
  exact (cacheFold_size trace.messageCalls memory.external.cache).trans (by
    change _ ≤ ((memory.external.hashCalls + trace.hashCalls : Nat) : ENNReal)
    rw [Nat.cast_add]
    exact add_le_add hbound hlength)

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem checkedHashResult_cacheSize (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (input : inputs) (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    QueryCache.enncard (checkedHashResult key.parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory.external.cache ≤
      QueryCache.enncard state.memory.external.cache + 1 := by
  have hp := congrArg (fun result : Option HashOutput × ResidualByteFrontend.State inputs => QueryCache.enncard result.2.memory.cache)
    (hashResult_project key.parameter inputs hencoding words publicReplies selections rows routing actual seed input state)
  have hr := congrArg (fun result : Option HashOutput × ExternalMemory => QueryCache.enncard result.2.cache)
    (ResidualByteFrontend.hashQueryResult_project key.parameter inputs words routing.disclosed routing.known
      (freshPrefix key.parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows)
      actual seed input (project state) hcovered
      (freshPrefix_local key.parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows input))
  change QueryCache.enncard (hashResult key.parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory.external.cache ≤ _
  apply hp.trans_le
  apply hr.trans_le
  generalize ResidualByteFrontend.publicCachedReply inputs
    (freshPrefix key.parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows)
    actual seed input (project state).memory = answer
  cases answer with
  | none => exact le_self_add
  | some answer => exact QueryCache.enncard_cacheQuery_le state.memory.external.cache input.val answer

theorem lazyByteRun_world_cacheSizeBound (routing : Routing) (input : OracleWorld.Domain)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (hbound : CacheSizeBound state.memory)
    (result : Option (OracleWorld.Range input) × State inputs)
    (hresult : lazyByteRun key.parameter inputs hencoding words publicReplies selections rows routing
      (liftM (OracleWorld.query input)) state result ≠ 0) : CacheSizeBound result.2.memory := by
  cases input with
  | inl input =>
      rw [← bind_pure (liftM (OracleWorld.query (.inl input))), lazyByteRun_random_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      rw [lazyByteRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hbound
  | inr input =>
      have hin : input ∈ inputs := hinputs (by
        rw [← bind_pure (liftM (OracleWorld.query (.inr input)))]
        exact mem_hashInputs_hash_bind input pure)
      obtain ⟨actual, seed, rfl⟩ := lazyByteRun_hash_result key.parameter inputs hencoding words publicReplies selections rows routing input hin state ha result hresult
      unfold CacheSizeBound
      rw [checkedHashResult_hashCalls, Nat.cast_add, Nat.cast_one]
      exact (checkedHashResult_cacheSize key inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state hcovered).trans
        (add_le_add hbound le_rfl)

variable (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem monitoredStep_cacheSizeBound (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs)
    (hvalid : MonitoredValid inputs state) (hinputs : requestInputs key input ⊆ inputs)
    (hbound : CacheSizeBound state.1.memory)
    (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs)
    (hresult : monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state result ≠ 0) :
    CacheSizeBound result.2.1.memory := by
  cases input with
  | inl input =>
      rw [monitoredStep, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      rw [lazyRun_externalProgram] at hraw
      exact lazyByteRun_world_cacheSizeBound key inputs hencoding words publicReplies selections rows state.1.memory.routing
        input hinputs state.1 hvalid.1 hvalid.2 hbound raw hraw
  | inr message =>
      rw [monitoredStep, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨annotation, _, hresult⟩ := hresult
      rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      have hin := digestInputs_of_request key inputs words selections message state.1.memory.routing.known hinputs
      obtain ⟨record, hr, hm⟩ := lazyRun_jointSigningProgram_memory_trace key.parameter inputs hencoding words publicReplies selections rows
        state.1.memory.routing key.root message (by simpa only [publicDigestLoop_eq] using hin) state.1 hvalid.1 hvalid.2 raw hraw
      have heq : raw = (some record, raw.2) := Prod.ext hr rfl
      rw [heq]
      change CacheSizeBound raw.2.memory
      rw [hm]
      exact hbound.applyBoundary record.2

theorem monitoredRun_cacheSizeBound {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : sourceInputs key computation ⊆ inputs) (hbound : CacheSizeBound state.1.memory)
    (result : Option Result × MonitoredState inputs)
    (hresult : monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state result ≠ 0) :
    CacheSizeBound result.2.1.memory := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [monitoredRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hbound
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨⟨answer, after⟩, hstep, hresult⟩ := hresult
      have hbound' := monitoredStep_cacheSizeBound key inputs hencoding words publicReplies selections rows budget required stopAfter
        input state hvalid ((requestInputs_subset key input next).trans hinputs) hbound (answer, after) hstep
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hbound'
      | some answer =>
          exact ih answer after
            (monitoredStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter input state hvalid (some answer, after) hstep)
            ((sourceInputs_next_subset key input next answer).trans hinputs) hbound' hresult

theorem initialMonitoredSource_cacheSizeBound (adversary : Adversary) (encoding : ReferenceEncodingAuxiliary)
    (dummy : OtsReferenceWords) (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy))
    (high : CanonicalGraphHighHalves) (stopped : Bool)
    (result : Option (Forgery × Bool) × MonitoredState (gameInputs adversary))
    (hresult : initialMonitoredSource key adversary encoding dummy exposed high budget required stopAfter stopped result ≠ 0) :
    CacheSizeBound result.2.1.memory := by
  apply monitoredRun_cacheSizeBound key (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows budget required stopAfter _ _
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
    (sourceInputs_unlogged_subset_gameInputs adversary key) _ result hresult
  change QueryCache.enncard (∅ : QueryCache HashSpec) ≤ (1212415 : ENNReal)
  rw [QueryCache.enncard_empty]
  exact zero_le

theorem initialMonitoredSource_proposalCacheBound (adversary : Adversary) (encoding : ReferenceEncodingAuxiliary)
    (dummy : OtsReferenceWords) (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy))
    (high : CanonicalGraphHighHalves) (stopped : Bool)
    (hparameter : key.parameter ∈ support sampleParameter) (hencoding' : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hcost : HasHashQueryBound scheme adversary budget) (hbudget : budget ≤ 2 ^ 127)
    (result : Option (Forgery × Bool) × MonitoredState (gameInputs adversary))
    (hresult : initialMonitoredSource key adversary encoding dummy exposed high budget required stopAfter stopped result ≠ 0)
    (halive : result.2.2.stopped = false) (hclean : ¬ CertificateCacheExceptional key result.2.1.memory.external.cache) :
    ProposalCacheBound key result.2.1.memory.external.cache result.2.2.spent := by
  have hsize := initialMonitoredSource_cacheSizeBound key budget required stopAfter adversary encoding dummy exposed high stopped result hresult
  have hspent := initialMonitoredSource_spent_eq key budget required stopAfter adversary encoding dummy exposed high stopped result hresult halive
  have htotal := initialMonitoredSource_hashCalls_le key adversary encoding dummy exposed high budget required stopAfter stopped
    hparameter hencoding' hroot hcost result hresult
  rw [hspent]
  exact proposalCacheBound_of_no_cache_exception key _ (Finite.of_enncard_le hsize) _ (htotal.trans hbudget) hsize hclean

end SphincsSecurity.Concrete.RetainedResidual

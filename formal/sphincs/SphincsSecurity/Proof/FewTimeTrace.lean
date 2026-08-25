import SphincsSecurity.Proof.TracedGame
import SphincsSecurity.Proof.FewTimeWitness
import SphincsSecurity.Proof.TerminalCache

/-!
# Few-time witnesses in the signing cache trace

The finite cover chooses ordinary signing-log entries. This module locates the corresponding
cache-trace entry, retaining the cache immediately before that signer invocation.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def signingCacheTraceFlatLog (trace : SigningCacheTrace) : List FlatSigningEntry :=
  trace.map fun entry => (entry.request, entry.signature)

theorem signingCacheTraceFlatLog_eq (trace : SigningCacheTrace) :
    signingCacheTraceFlatLog trace = trace.toSigningLog.map SigningEntry.flat := by
  induction trace with
  | nil => rfl
  | cons entry rest _ => simp [signingCacheTraceFlatLog,
      SigningCacheTrace.toSigningLog, SigningEntry.flat]

theorem exists_signingCacheEntry_of_flat_mem (trace : SigningCacheTrace)
    (entry : FlatSigningEntry) (hentry : entry ∈ signingCacheTraceFlatLog trace) :
    ∃ tracedEntry ∈ trace,
      (tracedEntry.request, tracedEntry.signature) = entry := by
  simpa only [signingCacheTraceFlatLog, List.mem_map] using hentry

noncomputable def FewTimeCover.cacheEntry {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (entry : cover.entries) : SigningCacheEntry := by
  exact trace.get ⟨cover.logIndex entry, by
    have hlength := congrArg List.length hlog
    simpa only [SigningCacheTrace.toSigningLog, List.length_map] using
      (show (cover.logIndex entry).val < trace.toSigningLog.length by
        rw [hlength]
        exact (cover.logIndex entry).isLt)⟩

theorem FewTimeCover.cacheEntry_mem {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (entry : cover.entries) : cover.cacheEntry trace hlog entry ∈ trace :=
  by
    exact List.get_mem trace _

theorem FewTimeCover.cacheEntry_flat {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (entry : cover.entries) :
    ((cover.cacheEntry trace hlog entry).request,
      (cover.cacheEntry trace hlog entry).signature) = entry.1 :=
  by
    let position := (cover.logIndex entry).val
    have htraceLength : trace.length = signingLog.length := by
      have hlength := congrArg List.length hlog
      simpa only [SigningCacheTrace.toSigningLog, List.length_map] using hlength
    have htraceLt : position < trace.length := by
      rw [htraceLength]
      exact (cover.logIndex entry).isLt
    have hlists : signingCacheTraceFlatLog trace = signingLog.map SigningEntry.flat := by
      rw [signingCacheTraceFlatLog_eq, hlog]
    have hget := congrArg (fun list : List FlatSigningEntry => list[position]?) hlists
    have hright : (signingLog.map SigningEntry.flat)[position]? = some entry.1 := by
      rw [List.getElem?_eq_getElem]
      · rw [List.getElem_map]
        simpa only [position, List.get_eq_getElem] using
          congrArg some (cover.logIndex_spec entry)
      · simpa only [position, List.length_map] using (cover.logIndex entry).isLt
    have hleft : (signingCacheTraceFlatLog trace)[position]? = some entry.1 := hget.trans hright
    rw [List.getElem?_eq_getElem (by
      simpa only [signingCacheTraceFlatLog, List.length_map] using htraceLt)] at hleft
    have hleft' := Option.some.inj hleft
    change (trace.map fun tracedEntry =>
      (tracedEntry.request, tracedEntry.signature))[position]'(by
        simpa only [List.length_map] using htraceLt) = entry.1 at hleft'
    rw [List.getElem_map] at hleft'
    simpa only [FewTimeCover.cacheEntry, position, List.get_eq_getElem] using hleft'

theorem FewTimeCover.cacheEntry_first_flat {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (entry : cover.entries) (earlier : Fin trace.length)
    (hearlier : earlier.val < (cover.logIndex entry).val) :
    ((trace.get earlier).request, (trace.get earlier).signature) ≠ entry.1 := by
  classical
  have hlists : signingCacheTraceFlatLog trace = signingLog.map SigningEntry.flat := by
    rw [signingCacheTraceFlatLog_eq, hlog]
  let flatEarlier : Fin (signingCacheTraceFlatLog trace).length :=
    ⟨earlier.val, by
      simpa only [signingCacheTraceFlatLog, List.length_map] using earlier.isLt⟩
  have hidx : (signingCacheTraceFlatLog trace).idxOf entry.1 =
      (cover.logIndex entry).val := by
    rw [hlists]
    rfl
  have hlt : flatEarlier.val < (signingCacheTraceFlatLog trace).idxOf entry.1 := by
    rw [hidx]
    exact hearlier
  have hne := List.get_ne_of_lt_idxOf
    (signingCacheTraceFlatLog trace) entry.1 flatEarlier hlt
  simpa only [flatEarlier, signingCacheTraceFlatLog, List.get_eq_getElem,
    List.getElem_map] using hne

theorem FewTimeCover.earlier_finalCache_le_cacheEntry_initialCache
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (hchronological : trace.Chronological) (entry : cover.entries)
    (earlier : Fin trace.length) (hearlier : earlier.val < (cover.logIndex entry).val) :
    (trace.get earlier).finalCache ≤ (cover.cacheEntry trace hlog entry).initialCache := by
  let selectedPosition : Fin trace.length := ⟨(cover.logIndex entry).val, by
    have hlength := congrArg List.length hlog
    simpa only [SigningCacheTrace.toSigningLog, List.length_map] using
      (show (cover.logIndex entry).val < trace.toSigningLog.length by
        rw [hlength]
        exact (cover.logIndex entry).isLt)⟩
  have hle := hchronological.get_finalCache_le_initialCache earlier selectedPosition hearlier
  simpa only [selectedPosition, FewTimeCover.cacheEntry] using hle

theorem FewTimeCover.cacheEntry_injective {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog) :
    Function.Injective (cover.cacheEntry trace hlog) := by
  intro left right heq
  apply Subtype.ext
  rw [← cover.cacheEntry_flat trace hlog left, ← cover.cacheEntry_flat trace hlog right, heq]

theorem FewTimeCover.cacheEntry_validRun {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (hvalid : trace.ValidRuns secretKey) (entry : cover.entries) :
    (cover.cacheEntry trace hlog entry).ValidRun secretKey :=
  hvalid _ (cover.cacheEntry_mem trace hlog entry)

theorem FewTimeCover.cacheEntry_cachesLe {f : QueryImpl HashSpec Id}
    {cache finalCache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (hcaches : trace.CachesLe finalCache) (entry : cover.entries) :
    (cover.cacheEntry trace hlog entry).initialCache ≤ finalCache
      ∧ (cover.cacheEntry trace hlog entry).finalCache ≤ finalCache :=
  hcaches _ (cover.cacheEntry_mem trace hlog entry)

theorem FewTimeCover.cacheEntry_request_signature {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (entry : cover.entries) :
    let selected := cover.select (cover.representativeTree entry)
    (cover.cacheEntry trace hlog entry).request = selected.entry.1
      ∧ (cover.cacheEntry trace hlog entry).signature = some selected.signature := by
  let selected := cover.select (cover.representativeTree entry)
  have hpair :
      ((cover.cacheEntry trace hlog entry).request,
        (cover.cacheEntry trace hlog entry).signature) = selected.entry.flat :=
    (cover.cacheEntry_flat trace hlog entry).trans
      (cover.representativeTree_spec entry).symm
  exact ⟨congrArg Prod.fst hpair, (congrArg Prod.snd hpair).trans selected.response_eq⟩

theorem FewTimeCover.cacheEntry_successfulSignRun {f : QueryImpl HashSpec Id}
    {cache finalCache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (hvalid : trace.ValidRuns secretKey) (hcaches : trace.CachesLe finalCache)
    (hf : finalCache.AgreesWithFn f) (entry : cover.entries) :
    let selected := cover.select (cover.representativeTree entry)
    SuccessfulSignRun f finalCache secretKey selected.entry.1 selected.signature := by
  let selected := cover.select (cover.representativeTree entry)
  have hfields := cover.cacheEntry_request_signature trace hlog entry
  have hrun := SigningCacheEntry.successfulSignRun
    (cover.cacheEntry_validRun trace hlog hvalid entry) hfields.2
    (cover.cacheEntry_cachesLe trace hlog hcaches entry).2 hf
  simpa only [hfields.1] using hrun

theorem FewTimeCover.cacheEntry_digest_cached {f : QueryImpl HashSpec Id}
    {cache finalCache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (hvalid : trace.ValidRuns secretKey) (hcaches : trace.CachesLe finalCache)
    (hf : finalCache.AgreesWithFn f) (entry : cover.entries) :
    (cover.cacheEntry trace hlog entry).finalCache (cover.entryDigestInput entry) ≠ none := by
  let tracedEntry := cover.cacheEntry trace hlog entry
  let selected := cover.select (cover.representativeTree entry)
  have hfields := cover.cacheEntry_request_signature trace hlog entry
  have hentryLe := (cover.cacheEntry_cachesLe trace hlog hcaches entry).2
  have hentryAgree : tracedEntry.finalCache.AgreesWithFn f :=
    fun _ _ hcached => hf (hentryLe hcached)
  have hrun := SigningCacheEntry.successfulSignRun
    (cover.cacheEntry_validRun trace hlog hvalid entry) hfields.2 le_rfl hentryAgree
  have hrun' : SuccessfulSignRun f tracedEntry.finalCache secretKey
      selected.entry.1 selected.signature := by
    simpa only [tracedEntry, selected, hfields.1] using hrun
  obtain ⟨_, _, _, hdigest, _, _, _, _, _, _, _⟩ := hrun'.indexed
  have hcached := CachedRun.messageDigest_cached hdigest.extract.2.choose_spec.2.2.2.2
  simpa only [FewTimeCover.entryDigestInput, selected, tracedEntry] using hcached

def FewTimeCover.EntryDigestPrecached {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (entry : cover.entries) : Prop :=
  (cover.cacheEntry trace hlog entry).initialCache (cover.entryDigestInput entry) ≠ none

theorem FewTimeCover.entryDigest_cache_miss_then_hit {f : QueryImpl HashSpec Id}
    {cache finalCache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (hvalid : trace.ValidRuns secretKey) (hcaches : trace.CachesLe finalCache)
    (hf : finalCache.AgreesWithFn f) (entry : cover.entries)
    (hfresh : ¬ cover.EntryDigestPrecached trace hlog entry) :
    (cover.cacheEntry trace hlog entry).initialCache (cover.entryDigestInput entry) = none
      ∧ (cover.cacheEntry trace hlog entry).finalCache (cover.entryDigestInput entry) ≠ none := by
  exact ⟨not_ne_iff.mp hfresh,
    cover.cacheEntry_digest_cached trace hlog hvalid hcaches hf entry⟩

theorem FewTimeCover.earlier_successful_digest_input_ne
    {f : QueryImpl HashSpec Id} {cache finalCache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (trace : SigningCacheTrace) (hlog : trace.toSigningLog = signingLog)
    (hvalid : trace.ValidRuns secretKey) (hcaches : trace.CachesLe finalCache)
    (hf : finalCache.AgreesWithFn f) (entry : cover.entries)
    (earlier : Fin trace.length)
    (hearlier : earlier.val < (cover.logIndex entry).val)
    (earlierSignature : Signature)
    (hresponse : (trace.get earlier).signature = some earlierSignature) :
    tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root (trace.get earlier).request
          earlierSignature.randomness)
      ≠ cover.entryDigestInput entry := by
  intro hinput
  let selected := cover.select (cover.representativeTree entry)
  have hearlierLe := (hcaches (trace.get earlier) (List.get_mem trace earlier)).2
  have hearlierRun := SigningCacheEntry.successfulSignRun
    (hvalid (trace.get earlier) (List.get_mem trace earlier)) hresponse hearlierLe hf
  have hselectedRun := cover.cacheEntry_successfulSignRun trace hlog hvalid hcaches hf entry
  have hpayload := (tweakableHashInput_injective secretKey.parameter (by trivial) (by trivial)
    hinput).2
  obtain ⟨hmessage, hrandomness⟩ := messageDigestPayload_injective secretKey.root hpayload
  have hsignature : earlierSignature = selected.signature :=
    successfulSignRun_signature_eq hearlierRun hselectedRun hmessage hrandomness
  have hflat := cover.cacheEntry_first_flat trace hlog entry earlier hearlier
  apply hflat
  rw [← cover.representativeTree_spec entry]
  apply Prod.ext
  · exact hmessage
  · change (trace.get earlier).signature = selected.entry.2
    exact hresponse.trans ((congrArg some hsignature).trans selected.response_eq.symm)

end SphincsSecurity.Concrete

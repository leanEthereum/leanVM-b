import SphincsSecurity.Proof.EncodingSignerLatent

/-!
# First latent encoding interval

The full adversary trace groups each direct query and each complete signer invocation into one
cache interval. The first interval that creates a latent encoding collision is either one direct
fresh hash query or a signer interval classified by `EncodingSignerLatent`.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

theorem FullAdversaryTrace.CacheChain.exists_first_event_interval
    {start finish : QueryCache HashSpec} {intervals : List AdversaryCacheEntry}
    (Event : QueryCache HashSpec → Prop)
    (hchain : FullAdversaryTrace.CacheChain start intervals finish)
    (hclean : ¬ Event start) (hevent : Event finish) :
    ∃ position : Fin intervals.length,
      ¬ Event (intervals.get position).initialCache
        ∧ Event (intervals.get position).finalCache := by
  induction intervals generalizing start finish with
  | nil =>
      change finish = start at hchain
      exact (hclean (hchain ▸ hevent)).elim
  | cons entry rest ih =>
      obtain ⟨rfl, hrest⟩ := hchain
      by_cases hentry : Event entry.finalCache
      · exact ⟨⟨0, by simp⟩, by simpa using hclean, by simpa using hentry⟩
      · obtain ⟨position, hpositionClean, hpositionEvent⟩ :=
          ih hrest hentry hevent
        exact ⟨Fin.succ position, by simpa using hpositionClean,
          by simpa using hpositionEvent⟩

namespace Concrete

inductive FirstLatentIntervalOutcome
    (secretKey : SecretKey) (entry : AdversaryCacheEntry) : Prop where
  | direct (input : HashInput) (answer : HashOutput)
      (initialCache finalCache : QueryCache HashSpec)
      (entryEq : entry = ⟨.inl (.inr input), answer, initialCache, finalCache⟩)
      (finalEq : finalCache = initialCache.cacheQuery input answer)
      (finiteInitial : Finite initialCache)
      (outcome : LatentEncodingStepOutcome initialCache
        finiteInitial secretKey input answer)
  | signer (request : SignRequest) (result : Option Signature)
      (initialCache finalCache : QueryCache HashSpec)
      (entryEq : entry = ⟨.inr request, result, initialCache, finalCache⟩)
      (outcome : LatentEncodingSignerIntervalOutcome
        initialCache finalCache secretKey)

theorem firstLatentIntervalOutcome
    {rootCache adversaryCache finalCache : QueryCache HashSpec}
    {secretKey : SecretKey} {trace : FullAdversaryTrace}
    (hchain : FullAdversaryTrace.CacheChain rootCache trace.intervals adversaryCache)
    (hvalid : trace.ValidIntervals secretKey)
    (hintervals : trace.IntervalsLe finalCache)
    (hfinite : Finite finalCache)
    (hstructuralClean : ¬ Bad secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret finalCache)
    (hclean : ¬ LatentEncodingBad rootCache secretKey)
    (hbad : LatentEncodingBad adversaryCache secretKey) :
    ∃ position : Fin trace.intervals.length,
      FirstLatentIntervalOutcome secretKey (trace.intervals.get position) := by
  obtain ⟨selected, hselectedClean, hselectedBad⟩ :=
    hchain.exists_first_event_interval (LatentEncodingBad · secretKey) hclean hbad
  let entry := trace.intervals.get selected
  have hentry : entry ∈ trace.intervals := List.get_mem _ selected
  have hinitialLe : entry.initialCache ≤ finalCache := (hintervals entry hentry).1
  have hfinalLe : entry.finalCache ≤ finalCache := (hintervals entry hentry).2
  have hfiniteInitial : Finite entry.initialCache := hfinite.of_le hinitialLe
  have hfiniteFinal : Finite entry.finalCache := hfinite.of_le hfinalLe
  have hinitialStructuralClean : ¬ Bad secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret entry.initialCache := by
    intro hbadInitial
    exact hstructuralClean (Bad.mono secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret hinitialLe hbadInitial)
  have hfinalStructuralClean : ¬ Bad secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret entry.finalCache := by
    intro hbadFinal
    exact hstructuralClean (Bad.mono secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret hfinalLe hbadFinal)
  change ¬ LatentEncodingBad entry.initialCache secretKey at hselectedClean
  change LatentEncodingBad entry.finalCache secretKey at hselectedBad
  refine ⟨selected, ?_⟩
  change FirstLatentIntervalOutcome secretKey entry
  obtain ⟨entryInput, entryOutput, initialCache, intervalFinalCache⟩ := entry
  cases entryInput with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          exfalso
          have hrun := hvalid _ hentry
          change (entryOutput, intervalFinalCache) ∈ support
            ((unifFwdImpl HashSpec uniformInput).run initialCache) at hrun
          have hforward :
              (unifFwdImpl HashSpec uniformInput).run initialCache =
                (fun sample => (sample, initialCache)) <$>
                  (liftM (unifSpec.query uniformInput) : ProbComp _) := by
            simpa [simulateQ_query] using
              (unifFwdImpl.simulateQ_run
                (hashSpec := HashSpec)
                (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache)
          rw [hforward, support_map] at hrun
          obtain ⟨sample, hsample, heq⟩ := hrun
          have hcacheEq : intervalFinalCache = initialCache :=
            (congrArg Prod.snd heq).symm
          exact hselectedClean (hcacheEq ▸ hselectedBad)
      | inr input =>
          change HashOutput at entryOutput
          by_cases hcached : initialCache input = none
          · have hfinalEq := FullAdversaryTrace.directHashInterval_eq_cacheQuery_of_fresh
              hvalid input entryOutput initialCache intervalFinalCache hentry hcached
            have hbadStep : LatentEncodingBad
                (initialCache.cacheQuery input entryOutput) secretKey := by
              rwa [← hfinalEq]
            exact .direct input entryOutput initialCache intervalFinalCache rfl hfinalEq
              hfiniteInitial
              (latentEncodingBad_step_paid_or_provisional hfiniteInitial
                hinitialStructuralClean hselectedClean hcached hbadStep)
          · obtain ⟨cachedAnswer, hcachedAnswer⟩ :=
              Option.ne_none_iff_exists'.mp hcached
            have hfinalEq :=
              (FullAdversaryTrace.directHashInterval_eq_of_cached hvalid input
                entryOutput cachedAnswer initialCache intervalFinalCache hentry
                hcachedAnswer).2
            exact (hselectedClean (hfinalEq ▸ hselectedBad)).elim
  | inr request =>
      change Option Signature at entryOutput
      have hrun := hvalid _ hentry
      change (entryOutput, intervalFinalCache) ∈ support
        ((simulateQ romImpl (sign secretKey request)).run initialCache) at hrun
      exact .signer request entryOutput initialCache intervalFinalCache rfl
        (latentEncodingBad_signerInterval_paid_or_pinned hfiniteFinal hrun
          hfinalStructuralClean hselectedClean hselectedBad)

end Concrete

end SphincsSecurity

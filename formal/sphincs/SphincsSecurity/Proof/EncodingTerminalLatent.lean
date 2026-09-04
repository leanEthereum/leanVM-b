import SphincsSecurity.Proof.EncodingTraceLatent

/-!
# Latent encoding creation through final verification

The fixed encoding position exposed by a terminal collision is traced through the adversary and the final verifier without discarding the fresh query that first creates it.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

namespace Concrete

inductive FinalLatentEncodingAtOutcome
    (secretKey : SecretKey) (position : EncodingPosition)
    (trace : FullAdversaryTrace) (adversaryCache finalCache : QueryCache HashSpec) : Prop where
  | adversary (source : Fin trace.intervals.length)
      (outcome : FirstLatentAtIntervalOutcome secretKey position
        (trace.intervals.get source))
  | verifier (cache : QueryCache HashSpec) (input : HashInput) (answer : HashOutput)
      (finiteCache : Finite cache)
      (adversaryLe : adversaryCache ≤ cache)
      (finalLe : cache.cacheQuery input answer ≤ finalCache)
      (stepClean : ¬ LatentEncodingBadAt cache secretKey position)
      (uncached : cache input = none)
      (stepBad : LatentEncodingBadAt
        (cache.cacheQuery input answer) secretKey position)
      (outcome : LatentEncodingAtStepOutcome cache finiteCache secretKey input answer position)

theorem firstLatentEncodingAt_finalOutcome
    {alpha : Type} {rootCache adversaryCache finalCache : QueryCache HashSpec}
    {secretKey : SecretKey} {trace : FullAdversaryTrace}
    {position : EncodingPosition} {verification : OracleComp OracleWorld alpha}
    {result : alpha}
    (hchain : FullAdversaryTrace.CacheChain rootCache trace.intervals adversaryCache)
    (hvalid : trace.ValidIntervals secretKey)
    (hintervals : trace.IntervalsLe finalCache)
    (hfinite : Finite finalCache)
    (hstructuralClean : ¬ Bad secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret finalCache)
    (hrootClean : ¬ LatentEncodingBadAt rootCache secretKey position)
    (hrun : (result, finalCache) ∈ support
      ((simulateQ romImpl verification).run adversaryCache))
    (hbad : LatentEncodingBadAt finalCache secretKey position) :
    FinalLatentEncodingAtOutcome secretKey position trace adversaryCache finalCache := by
  by_cases hadversaryBad : LatentEncodingBadAt adversaryCache secretKey position
  · obtain ⟨source, houtcome⟩ := firstLatentAtIntervalOutcome hchain hvalid hintervals
      hfinite hstructuralClean hrootClean hadversaryBad
    exact .adversary source houtcome
  · obtain ⟨cache, input, answer, hadversaryLe, hstepClean, huncached, hstepBad,
      hfinalLe⟩ := freshBadStep_of_mem_support
        (fun cache => LatentEncodingBadAt cache secretKey position)
        verification adversaryCache result finalCache hrun hadversaryBad hbad
    have hfiniteCache : Finite cache :=
      hfinite.of_le ((le_cacheQuery huncached).trans hfinalLe)
    have hstepStructuralClean : ¬ Bad secretKey.parameter secretKey.otsSecret
        secretKey.ftsSecret cache := by
      intro hbadCache
      exact hstructuralClean (Bad.mono secretKey.parameter secretKey.otsSecret
        secretKey.ftsSecret ((le_cacheQuery huncached).trans hfinalLe) hbadCache)
    exact .verifier cache input answer hfiniteCache hadversaryLe hfinalLe hstepClean
      huncached hstepBad
      (latentEncodingBadAt_step_paid_or_provisional hfiniteCache hstepStructuralClean
        hstepClean huncached hstepBad)

theorem encodingBad_finalOutcome
    {alpha : Type} {rootCache adversaryCache finalCache : QueryCache HashSpec}
    {secretKey : SecretKey} {trace : FullAdversaryTrace}
    {verification : OracleComp OracleWorld alpha} {result : alpha}
    (hchain : FullAdversaryTrace.CacheChain rootCache trace.intervals adversaryCache)
    (hvalid : trace.ValidIntervals secretKey)
    (hintervals : trace.IntervalsLe finalCache)
    (hfinite : Finite finalCache)
    (hstructuralClean : ¬ Bad secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret finalCache)
    (hrootEncodingNone : ∀ (position : EncodingPosition) (payload : HashInput),
      rootCache (tweakableHashInput secretKey.parameter position.domain payload) = none)
    (hrun : (result, finalCache) ∈ support
      ((simulateQ romImpl verification).run adversaryCache))
    (hbad : EncodingBad finalCache secretKey) :
    ∃ position : EncodingPosition,
      HasEncodingTarget finalCache secretKey position ∧
        FinalLatentEncodingAtOutcome secretKey position trace adversaryCache finalCache := by
  obtain ⟨position, htarget, hlatent⟩ := hbad.latent_with_target
  have hrootClean : ¬ LatentEncodingBadAt rootCache secretKey position := by
    intro hrootBad
    exact not_latentEncodingBad_of_encoding_none hrootEncodingNone ⟨position, hrootBad⟩
  exact ⟨position, htarget,
    firstLatentEncodingAt_finalOutcome hchain hvalid hintervals hfinite
      hstructuralClean hrootClean hrun hlatent⟩

end Concrete

end SphincsSecurity

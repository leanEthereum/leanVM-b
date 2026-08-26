import SphincsSecurity.Proof.EncodingStageCharge
import SphincsSecurity.Proof.FirstBad

/-!
# Latent encoding collisions inside a signer

A provisional latent collision created inside one signer invocation cannot remain provisional at
the invocation boundary. Its fresh admissible input is exactly one of that signer's encoding
queries, so the complete retry search pins the canonical target before the signer returns.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem hasEncodingTarget_of_latent_creation_during_sign
    {secretKey : SecretKey} {message : Message}
    {initialCache cache finalCache : QueryCache HashSpec}
    {result : Option Signature} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition}
    (hrun : (result, finalCache) ∈ support
      ((simulateQ romImpl (sign secretKey message)).run initialCache))
    (hinitial : initialCache ≤ cache)
    (hfinal : cache.cacheQuery input answer ≤ finalCache)
    (hclean : ¬ LatentEncodingBad cache secretKey)
    (huncached : cache input = none)
    (hposition : AtEncodingPosition secretKey.parameter input position)
    (hbad : LatentEncodingBad (cache.cacheQuery input answer) secretKey) :
    HasEncodingTarget finalCache secretKey position := by
  obtain ⟨payload, hpayload⟩ := hposition
  have hinitialMiss : initialCache
      (tweakableHashInput secretKey.parameter position.domain payload) = none := by
    rw [← hpayload]
    by_contra hcached
    obtain ⟨cachedAnswer, hcachedAnswer⟩ := Option.ne_none_iff_exists'.mp hcached
    have := hinitial hcachedAnswer
    rw [huncached] at this
    simp at this
  have hfinalCached : finalCache
      (tweakableHashInput secretKey.parameter position.domain payload) = some answer := by
    rw [← hpayload]
    exact hfinal (by simp)
  have hvalid : TargetSum.ValidDigest (truncateHash answer) := by
    by_contra hinvalid
    exact hclean (hbad.of_cacheQuery_of_invalid_encoding huncached
      ⟨payload, hpayload⟩ hinvalid)
  apply hasEncodingTarget_of_sign_transition secretKey message initialCache finalCache result
    hrun position payload hinitialMiss
  · simp [hfinalCached]
  · simpa [fromCache, hfinalCached] using hvalid

inductive LatentEncodingSignerStepOutcome
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (input : HashInput) (answer : HashOutput) (finalCache : QueryCache HashSpec) : Prop where
  | existingTarget (position : EncodingPosition)
      (atPosition : AtEncodingPosition secretKey.parameter input position)
      (target : HasEncodingTarget cache secretKey position)
  | pinnedAtEnd (position : EncodingPosition)
      (atPosition : AtEncodingPosition secretKey.parameter input position)
      (target : HasEncodingTarget finalCache secretKey position)
  | paid (targets : Finset Digest)
      (hit : truncateHash answer ∈ targets)
      (drop : encodingStructuralPotential (cache.cacheQuery input answer) secretKey +
          targets.card ≤ encodingStructuralPotential cache secretKey)

theorem latentEncodingBad_step_paid_or_pinned_by_sign
    {secretKey : SecretKey} {message : Message}
    {initialCache cache finalCache : QueryCache HashSpec}
    {result : Option Signature} {input : HashInput} {answer : HashOutput}
    (hfinite : Finite cache)
    (hrun : (result, finalCache) ∈ support
      ((simulateQ romImpl (sign secretKey message)).run initialCache))
    (hinitial : initialCache ≤ cache)
    (hfinal : cache.cacheQuery input answer ≤ finalCache)
    (hstructuralClean : ¬ Bad secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache)
    (hclean : ¬ LatentEncodingBad cache secretKey)
    (huncached : cache input = none)
    (hbad : LatentEncodingBad (cache.cacheQuery input answer) secretKey) :
    LatentEncodingSignerStepOutcome cache secretKey input answer finalCache := by
  rcases latentEncodingBad_step_paid_or_provisional hfinite hstructuralClean hclean
    huncached hbad with ⟨position, hposition, htarget⟩ |
      ⟨position, hposition, hnotTarget, hstillNotTarget, hhit⟩ |
      ⟨targets, hhit, hdrop⟩
  · exact .existingTarget position hposition htarget
  · exact .pinnedAtEnd position hposition
      (hasEncodingTarget_of_latent_creation_during_sign hrun hinitial hfinal hclean
        huncached hposition hbad)
  · exact .paid targets hhit hdrop

inductive LatentEncodingSignerIntervalOutcome
    (initialCache finalCache : QueryCache HashSpec) (secretKey : SecretKey) : Prop where
  | pinned (position : EncodingPosition)
      (target : HasEncodingTarget finalCache secretKey position)
  | paid (cache : QueryCache HashSpec) (input : HashInput) (answer : HashOutput)
      (targets : Finset Digest)
      (initialLe : initialCache ≤ cache)
      (finalLe : cache.cacheQuery input answer ≤ finalCache)
      (hit : truncateHash answer ∈ targets)
      (drop : encodingStructuralPotential (cache.cacheQuery input answer) secretKey +
          targets.card ≤ encodingStructuralPotential cache secretKey)

theorem latentEncodingBad_signerInterval_paid_or_pinned
    {secretKey : SecretKey} {message : Message}
    {initialCache finalCache : QueryCache HashSpec} {result : Option Signature}
    (hfinite : Finite finalCache)
    (hrun : (result, finalCache) ∈ support
      ((simulateQ romImpl (sign secretKey message)).run initialCache))
    (hstructuralClean : ¬ Bad secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret finalCache)
    (hclean : ¬ LatentEncodingBad initialCache secretKey)
    (hbad : LatentEncodingBad finalCache secretKey) :
    LatentEncodingSignerIntervalOutcome initialCache finalCache secretKey := by
  obtain ⟨cache, input, answer, hinitial, hstepClean, huncached, hstepBad,
    hfinal⟩ := freshBadStep_of_mem_support (LatentEncodingBad · secretKey)
      (sign secretKey message) initialCache result finalCache hrun hclean hbad
  have hfiniteCache : Finite cache := hfinite.of_le
    ((le_cacheQuery huncached).trans hfinal)
  have hstepStructuralClean : ¬ Bad secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache := by
    intro hbadCache
    exact hstructuralClean (Bad.mono secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret ((le_cacheQuery huncached).trans hfinal) hbadCache)
  rcases latentEncodingBad_step_paid_or_pinned_by_sign hfiniteCache hrun hinitial
    hfinal hstepStructuralClean hstepClean huncached hstepBad with
    ⟨position, hposition, htarget⟩ | ⟨position, hposition, htarget⟩ |
      ⟨targets, hhit, hdrop⟩
  · exact .pinned position (htarget.mono ((le_cacheQuery huncached).trans hfinal))
  · exact .pinned position htarget
  · exact .paid cache input answer targets hinitial hfinal hhit hdrop

end SphincsSecurity.Concrete

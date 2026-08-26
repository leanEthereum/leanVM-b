import SphincsSecurity.Proof.EncodingStageCharge

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

end SphincsSecurity.Concrete

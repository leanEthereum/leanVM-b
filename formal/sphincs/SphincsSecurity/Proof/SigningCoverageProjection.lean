import SphincsSecurity.Proof.CollisionCoveragePotential
import SphincsSecurity.Proof.SelectedDigestCache

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem cacheMessageWeight_messageAnswers_congr (parameter : PublicParameter)
    (before after : QueryCache HashSpec) (hanswers : messageAnswers parameter before = messageAnswers parameter after)
    (weight : HashInput → FewTimeView → ENNReal) :
    cacheMessageWeight parameter weight before = cacheMessageWeight parameter weight after := by
  apply tsum_congr
  intro input
  by_cases hm : MessageHashInput parameter input
  · obtain ⟨payload, rfl⟩ := hm
    have heq := congrFun hanswers payload
    change before (tweakableHashInput parameter .message payload) = after (tweakableHashInput parameter .message payload) at heq
    simp only [cacheMessageEntryWeight, heq]
  · unfold cacheMessageEntryWeight
    cases before input <;> cases after input <;> simp [hm]

theorem targetIndexMoments_messageAnswers_congr (key : SecretKey) (before after : QueryCache HashSpec)
    (hanswers : messageAnswers key.parameter before = messageAnswers key.parameter after) (log : QueryLog SigningSpec) :
    targetIndexMoments key before log = targetIndexMoments key after log := by
  funext power degree
  unfold targetIndexMoments
  rw [hanswers]
  apply Finset.sum_congr rfl
  intro index _
  rw [cachedIndexMultiplicity, cachedIndexMultiplicity, cacheMessageWeight_messageAnswers_congr _ _ _ hanswers]

theorem targetShapeMoments_messageAnswers_congr (key : SecretKey) (before after : QueryCache HashSpec)
    (hanswers : messageAnswers key.parameter before = messageAnswers key.parameter after)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) :
    targetShapeMoments key before log payload target = targetShapeMoments key after log payload target := by
  funext groups remaining
  unfold targetShapeMoments normalizedTargetLogProduct normalizedTargetLogMatch
  rw [hanswers]
  congr 1
  apply Finset.prod_congr rfl
  intro group _
  simp only [normalizedCachedTargetSubsetMatch_eq_weight]
  exact cacheMessageWeight_messageAnswers_congr _ _ _ hanswers _

theorem remainingCoveragePotential_messageAnswers_congr (key : SecretKey) (cap budget : Nat)
    (before after : QueryCache HashSpec) (hanswers : messageAnswers key.parameter before = messageAnswers key.parameter after)
    (log : QueryLog SigningSpec) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    remainingCoveragePotential key cap budget (before, log) groups remaining =
      remainingCoveragePotential key cap budget (after, log) groups remaining := by
  have hraw : observedRawIndexShapeVector key (before, log) = observedRawIndexShapeVector key (after, log) :=
    congrArg liftTargetIndexVector (targetIndexMoments_messageAnswers_congr key before after hanswers log)
  have htarget (payload : HashInput) (target : FewTimeView) :
      observedTargetShapeVector key payload target (before, log) = observedTargetShapeVector key payload target (after, log) :=
    targetShapeMoments_messageAnswers_congr key before after hanswers log payload target
  unfold remainingCoveragePotential cappedRemainingCachedTargetEnvelope cappedRemainingRawIndexEnvelope
  simp only
  split_ifs
  · simp only [remainingRawIndexEnvelope, hraw, remainingCachedTargetEnvelope, remainingTargetEnvelope, htarget]
    rw [cacheMessageWeight_messageAnswers_congr _ _ _ hanswers]
  · rfl

def SigningMetadataLE (first second : SigningEntry) : Prop :=
  first.1 = second.1 ∧ ∀ signature, first.2 = some signature →
    ∃ other, second.2 = some other ∧ signature.randomness = other.randomness

theorem SigningMetadataLE.refl (entry : SigningEntry) : SigningMetadataLE entry entry :=
  ⟨rfl, fun signature h => ⟨signature, h, rfl⟩⟩

theorem SigningMetadataLE.observed {first second : SigningEntry} (h : SigningMetadataLE first second)
    (answers : HashInput → Option HashOutput) (root : Digest) (source : FewTimeView)
    (hsource : observedSigningView? answers root first = some source) :
    observedSigningView? answers root second = some source := by
  cases hs : first.2 with
  | none => simp [observedSigningView?, hs] at hsource
  | some signature =>
      obtain ⟨other, ho, hr⟩ := h.2 signature hs
      simpa [observedSigningView?, hs, ho, h.1, hr] using hsource

theorem SigningMetadataLE.eligible {first second : SigningEntry} (h : SigningMetadataLE first second)
    (answers : HashInput → Option HashOutput) (root : Digest) (payload : HashInput) (source : FewTimeView)
    (hsource : eligibleSigningView? answers root payload first = some source) :
    eligibleSigningView? answers root payload second = some source := by
  cases hs : first.2 with
  | none => simp [eligibleSigningView?, hs] at hsource
  | some signature =>
      obtain ⟨other, ho, hr⟩ := h.2 signature hs
      simpa [eligibleSigningView?, observedSigningView?, hs, ho, h.1, hr] using hsource

private theorem signingMetadata_indicator_sum_le (first second : QueryLog SigningSpec)
    (hlog : List.Forall₂ SigningMetadataLE first second) (predicate : SigningEntry → Prop)
    [DecidablePred predicate]
    (hpredicate : ∀ entry other, SigningMetadataLE entry other → predicate entry → predicate other) :
    (first.map (fun entry => if predicate entry then 1 else 0)).sum ≤
      (second.map (fun entry => if predicate entry then 1 else 0)).sum := by
  induction hlog with
  | nil => exact le_rfl
  | @cons entry other first second hentry _ ih =>
      simp only [List.map_cons, List.sum_cons]
      apply Nat.add_le_add ?_ ih
      by_cases hp : predicate entry
      · simp only [if_pos hp, if_pos (hpredicate entry other hentry hp), le_refl]
      · simp only [if_neg hp, Nat.zero_le]

theorem targetIndexMoments_metadata_mono (key : SecretKey) (cache : QueryCache HashSpec)
    (first second : QueryLog SigningSpec) (hlog : List.Forall₂ SigningMetadataLE first second) (power degree : Nat) :
    targetIndexMoments key cache first power degree ≤ targetIndexMoments key cache second power degree := by
  apply Finset.sum_le_sum
  intro index _
  apply mul_le_mul' le_rfl
  apply pow_le_pow_left'
  apply Nat.cast_le.mpr
  change (signingSlotsAtIndex (fun slot => observedSigningView? (messageAnswers key.parameter cache) key.root (first.get slot)) index).card ≤
    (signingSlotsAtIndex (fun slot => observedSigningView? (messageAnswers key.parameter cache) key.root (second.get slot)) index).card
  rw [signingSlotsAtIndex_log_card first (observedSigningView? (messageAnswers key.parameter cache) key.root),
    signingSlotsAtIndex_log_card second (observedSigningView? (messageAnswers key.parameter cache) key.root)]
  apply signingMetadata_indicator_sum_le first second hlog
    (fun entry => ∃ source, observedSigningView? (messageAnswers key.parameter cache) key.root entry = some source ∧ source.1 = index)
  rintro entry other hentry ⟨source, hsource, hindex⟩
  exact ⟨source, hentry.observed _ _ _ hsource, hindex⟩

theorem targetShapeMoments_metadata_mono (key : SecretKey) (cache : QueryCache HashSpec)
    (first second : QueryLog SigningSpec) (hlog : List.Forall₂ SigningMetadataLE first second)
    (payload : HashInput) (target : FewTimeView) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetShapeMoments key cache first payload target groups remaining ≤
      targetShapeMoments key cache second payload target groups remaining := by
  apply mul_le_mul' le_rfl
  apply Finset.prod_le_prod'
  intro tree _
  apply mul_le_mul' le_rfl
  apply Nat.cast_le.mpr
  change targetTreeMatchCount (fun slot => eligibleSigningView? (messageAnswers key.parameter cache) key.root payload (first.get slot)) target tree ≤
    targetTreeMatchCount (fun slot => eligibleSigningView? (messageAnswers key.parameter cache) key.root payload (second.get slot)) target tree
  rw [targetTreeMatchCount_log first (eligibleSigningView? (messageAnswers key.parameter cache) key.root payload),
    targetTreeMatchCount_log second (eligibleSigningView? (messageAnswers key.parameter cache) key.root payload)]
  apply signingMetadata_indicator_sum_le first second hlog
    (fun entry => ∃ source, eligibleSigningView? (messageAnswers key.parameter cache) key.root payload entry = some source ∧
      source.1 = target.1 ∧ source.2 tree = target.2 tree)
  rintro entry other hentry ⟨source, hsource, hindex, htree⟩
  exact ⟨source, hentry.eligible _ _ _ _ hsource, hindex, htree⟩

theorem remainingCoveragePotential_metadata_mono (key : SecretKey) (cap budget : Nat) (cache : QueryCache HashSpec)
    (first second : QueryLog SigningSpec) (hlog : List.Forall₂ SigningMetadataLE first second)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    remainingCoveragePotential key cap budget (cache, first) groups remaining ≤
      remainingCoveragePotential key cap budget (cache, second) groups remaining := by
  have hlength := hlog.length_eq
  have hv : SigningTranscript.Valid first ↔ SigningTranscript.Valid second := by
    simp only [SigningTranscript.Valid, hlength]
  unfold remainingCoveragePotential cappedRemainingCachedTargetEnvelope cappedRemainingRawIndexEnvelope
  simp only [hv, hlength]
  split_ifs
  · apply add_le_add
    · apply cacheMessageWeight_mono
      intro input target
      apply targetShapeEnvelope_mono _ _ _ _ _ ?_ groups remaining hvalid
      intro G R _
      exact targetShapeMoments_metadata_mono key cache first second hlog _ target G R
    · apply mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
      apply targetShapeEnvelope_mono _ _ _ _ _ ?_ groups remaining hvalid
      intro G R _
      exact targetIndexMoments_metadata_mono key cache first second hlog G.card R.card
  · exact le_rfl

theorem signAfterDigest_remainingCoveragePotential_le (key : SecretKey) (cap budget : Nat)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) (before after : QueryCache HashSpec)
    (signature : Option Signature) (hfinish : (signature, after) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) (signAfterDigest key randomness index leaves)).run before))
    (message : Message) (log : QueryLog SigningSpec) (representative : Signature) (hrandomness : representative.randomness = randomness)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    remainingCoveragePotential key cap budget (after, log ++ [⟨message, signature⟩]) groups remaining ≤
      remainingCoveragePotential key cap budget (before, log ++ [⟨message, some representative⟩]) groups remaining := by
  have hanswers : messageAnswers key.parameter after = messageAnswers key.parameter before :=
    funext (signAfterDigest_message_cache_eq key randomness index leaves before after signature hfinish)
  rw [remainingCoveragePotential_messageAnswers_congr key cap budget after before hanswers]
  apply remainingCoveragePotential_metadata_mono key cap budget before _ _ ?_ groups remaining hvalid
  apply List.rel_append
  · induction log with
    | nil => exact List.Forall₂.nil
    | cons entry log ih => exact List.Forall₂.cons (SigningMetadataLE.refl entry) ih
  · refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
    intro actual hactual
    change signature = some actual at hactual
    refine ⟨representative, rfl, ?_⟩
    rw [hactual] at hfinish
    exact (signAfterDigest_support_some_randomness key randomness index leaves before after actual hfinish).trans hrandomness.symm

theorem remainingCoveragePotential_append_some_randomness_congr (key : SecretKey) (cap budget : Nat)
    (cache : QueryCache HashSpec) (message : Message) (log : QueryLog SigningSpec) (first second : Signature)
    (hrandomness : first.randomness = second.randomness)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    remainingCoveragePotential key cap budget (cache, log ++ [⟨message, some first⟩]) groups remaining =
      remainingCoveragePotential key cap budget (cache, log ++ [⟨message, some second⟩]) groups remaining := by
  have hle (a b : Signature) (hr : a.randomness = b.randomness) :
      remainingCoveragePotential key cap budget (cache, log ++ [⟨message, some a⟩]) groups remaining ≤
        remainingCoveragePotential key cap budget (cache, log ++ [⟨message, some b⟩]) groups remaining := by
    apply remainingCoveragePotential_metadata_mono key cap budget cache _ _ ?_ groups remaining hvalid
    apply List.rel_append
    · induction log with
      | nil => exact List.Forall₂.nil
      | cons entry log ih => exact List.Forall₂.cons (SigningMetadataLE.refl entry) ih
    · refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
      intro actual hactual
      have heq : a = actual := Option.some.inj hactual
      exact ⟨b, rfl, heq ▸ hr⟩
  exact le_antisymm (hle first second hrandomness) (hle second first hrandomness.symm)

theorem signAfterDigest_remainingCoveragePotential_eq (key : SecretKey) (cap budget : Nat)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) (before after : QueryCache HashSpec)
    (signature : Signature) (hfinish : (some signature, after) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) (signAfterDigest key randomness index leaves)).run before))
    (message : Message) (log : QueryLog SigningSpec) (representative : Signature) (hrandomness : representative.randomness = randomness)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    remainingCoveragePotential key cap budget (after, log ++ [⟨message, some signature⟩]) groups remaining =
      remainingCoveragePotential key cap budget (before, log ++ [⟨message, some representative⟩]) groups remaining := by
  have hanswers : messageAnswers key.parameter after = messageAnswers key.parameter before :=
    funext (signAfterDigest_message_cache_eq key randomness index leaves before after (some signature) hfinish)
  rw [remainingCoveragePotential_messageAnswers_congr key cap budget after before hanswers]
  exact remainingCoveragePotential_append_some_randomness_congr key cap budget before message log signature representative
    ((signAfterDigest_support_some_randomness key randomness index leaves before after signature hfinish).trans hrandomness.symm)
    groups remaining hvalid

-- Only randomness is read by the coverage potential.
def coverageSignature (randomness : Randomness) : Signature where
  randomness := randomness
  ftsSecret := fun _ => 0
  ftsPath := fun _ _ => 0
  counter := fun _ => 0
  chainValue := fun _ _ => 0
  authPath := fun _ => 0

def digestSelectionCoverageState (message : Message) (log : QueryLog SigningSpec)
    (result : Option (Randomness × Index × (DigestTree → FtsLeaf)) × QueryCache HashSpec) : CoverLogState :=
  (result.2, log ++ [⟨message, result.1.map (fun selected => coverageSignature selected.1)⟩])

theorem SigningDigestsCached.after_digestSelection (key : SecretKey) (message : Message) (attempts : Nat)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter cache key.root log)
    (result : Option (Randomness × Index × (DigestTree → FtsLeaf)) × QueryCache HashSpec)
    (hr : result ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run cache)) :
    SigningDigestsCached key.parameter (digestSelectionCoverageState message log result).1 key.root
      (digestSelectionCoverageState message log result).2 := by
  have hcache := simulateQ_romImpl_cache_le (signDigestLoop attempts key message) cache result hr
  have hprior := hsigned.mono hcache
  rcases result with ⟨selected, after⟩
  intro entry hentry signature hsignature
  rcases List.mem_append.mp hentry with hentry | hentry
  · exact hprior entry hentry signature hsignature
  · have heq := List.mem_singleton.mp hentry
    subst entry
    cases selected with
    | none => simp at hsignature
    | some data =>
        rcases data with ⟨randomness, index, leaves⟩
        have heq : coverageSignature randomness = signature := Option.some.inj hsignature
        obtain ⟨output, ho, _, _⟩ := signDigestLoop_selected_cached_output attempts key message cache after randomness index leaves hr
        rw [← heq]
        change after (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) ≠ none
        rw [ho]
        exact Option.some_ne_none output

end SphincsSecurity.Concrete

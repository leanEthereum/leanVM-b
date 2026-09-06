import SphincsSecurity.Proof.FtsProbeJointSigner

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem cacheMapCommutes_native_simulateQ_ordinaryRom
    (parameter : PublicParameter) (table : Coordinate → Digest) (ftsCache : SplitHashCache)
    (computation : OracleComp OracleWorld α) (hordinary : RomOrdinaryOnly parameter table computation) :
    OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table ftsCache)
      (simulateQ OtsProbeSimulation.ordinaryRomImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simpa only [simulateQ_pure] using OtsProbeSimulation.CacheMapCommutes.pure (nativeCacheProjection parameter table ftsCache) value
  | query_bind input next ih =>
      rw [RomOrdinaryOnly, isQueryBoundP_query_bind_iff] at hordinary
      rw [simulateQ_bind, simulateQ_spec_query]
      cases input with
      | inl n =>
          apply (OtsProbeSimulation.CacheMapCommutes.liftM (nativeCacheProjection parameter table ftsCache)
            (LazyRevealProbe.uniformQuery (Coordinate := OtsProbeSimulation.Coordinate) n)).bind
          intro output
          exact ih output (by simpa [RomOrdinaryOnly] using hordinary.2 output)
      | inr input =>
          apply (cacheMapCommutes_native_ordinaryHash parameter table ftsCache input
            (by simpa [NonOrdinaryInput] using hordinary.1)).bind
          intro output
          exact ih output (by simpa [RomOrdinaryOnly, NonOrdinaryInput] using hordinary.2 output)

theorem cacheMapCommutes_native_signDigestLoop
    (secretKey : SecretKey) (table : Coordinate → Digest) (ftsCache : SplitHashCache)
    (message : Message) (attempts : Nat) :
    OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection secretKey.parameter table ftsCache)
      (simulateQ OtsProbeSimulation.ordinaryRomImpl (signDigestLoop attempts secretKey message)) :=
  cacheMapCommutes_native_simulateQ_ordinaryRom secretKey.parameter table ftsCache _
    (romOrdinaryOnly_signDigestLoop attempts secretKey table message)

def jointDigestKey (parameter : PublicParameter) (root : Digest) : SecretKey :=
  ⟨parameter, root, fun _ _ _ _ => 0, fun _ _ _ => 0⟩

noncomputable def maskedJointSign (parameter : PublicParameter) (root : Digest) (message : Message) :
    NativeFtsStep (Option Signature) :=
  bindNativeSteps
    (liftNativeBlock (simulateQ OtsProbeSimulation.ordinaryRomImpl
      (signDigestLoop digestAttemptLimit (jointDigestKey parameter root) message))) fun selected =>
    match selected with
    | none => liftNativeBlock (pure none)
    | some (randomness, index, leaves) => maskedJointSignAfterDigest parameter randomness index leaves

attribute [local irreducible] signDigestLoop

theorem coupled_maskedJointSign
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest) (message : Message)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) :
    NativeStepCoupledAt parameter table state ftsFuel (maskedJointSign parameter root message)
      (OtsProbeSimulation.maskedPublishedChronologicalSign parameter root (fun index tree leaf => table (index, tree, leaf)) message)
      context fuel history cache ftsCache := by
  have hloop : signDigestLoop digestAttemptLimit
      (⟨parameter, root, fun _ _ _ _ => 0, fun index tree leaf => table (index, tree, leaf)⟩ : SecretKey) message =
      signDigestLoop digestAttemptLimit (jointDigestKey parameter root) message :=
    signDigestLoop_secretKeyWithFtsTable digestAttemptLimit (jointDigestKey parameter root) table message
  unfold OtsProbeSimulation.maskedPublishedChronologicalSign
  dsimp only
  rw [hloop]
  unfold maskedJointSign
  apply nativeStepCoupledAt_bind parameter table state ftsFuel _ _ _ _ context fuel history cache ftsCache hclean
    (liftNativeBlock_probeFree _ context fuel history cache)
  · exact projectNativeStepCache_liftNativeBlock parameter table state ftsFuel ftsCache _
      (cacheMapCommutes_native_signDigestLoop (jointDigestKey parameter root) table ftsCache message digestAttemptLimit)
      context fuel history cache hclean
  · intro finalState entry finalCache hresult
    obtain ⟨hstate, hsynced', _⟩ := invariants_liftNativeBlock parameter table state finalState ftsFuel _
      (fun cache => cacheMapCommutes_native_signDigestLoop (jointDigestKey parameter root) table cache message digestAttemptLimit)
      context fuel history cache ftsCache finalCache (some entry) hsynced hresult
    have hclean' : AdaptiveRevealProbe.tableHits finalState table = false := by simpa [hstate] using hclean
    cases hselected : entry.value.1 with
    | none =>
        exact projectNativeStepCache_liftNativeBlock parameter table finalState ftsFuel finalCache (pure none)
          (OtsProbeSimulation.CacheMapCommutes.pure _ none) entry.context entry.remaining entry.history entry.value.2 hclean'
    | some selected =>
        rcases selected with ⟨randomness, index, leaves⟩
        exact coupled_maskedJointSignAfterDigest parameter table randomness index leaves finalState ftsFuel
          entry.context entry.remaining entry.history entry.value.2 finalCache hclean' hsynced'

end SphincsSecurity.Concrete.FtsProbeSimulation

import SphincsSecurity.Proof.FtsProbeStablePrefixQueries
import SphincsSecurity.Proof.OtsProbeTrace

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def verifierFtsPrefix (publicKey : PublicKey) (message : Message) (signature : Signature) :
    OracleComp HashSpec (Option (MessageDigest × Digest)) := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  if ¬Admissible digest then pure none
  else
    let root ← ftsRecover publicKey.parameter (digestIndex digest) (digestLeaves digest) signature.ftsSecret signature.ftsPath
    pure (some (digest, root))

noncomputable def verifierAfterFts (publicKey : PublicKey) (signature : Signature) :
    Option (MessageDigest × Digest) → OracleComp HashSpec Bool
  | none => pure false
  | some (digest, root) => do
      match ← verifyLayers publicKey.parameter (digestIndex digest) signature numLayers root with
      | none => pure false
      | some value => pure (decide (value = publicKey.root))

theorem verify_eq_ftsPrefix (publicKey : PublicKey) (message : Message) (signature : Signature) :
    verify (m := OracleComp HashSpec) publicKey message signature =
      verifierFtsPrefix publicKey message signature >>= verifierAfterFts publicKey signature := by
  rw [verify_eq, verifierFtsPrefix, bind_assoc]
  apply bind_congr
  intro digest
  split_ifs <;> simp [verifierAfterFts]
  apply bind_congr
  intro root
  apply bind_congr
  intro result
  cases result <;> rfl

theorem queriesStable_verifierFtsPrefix
    (f : QueryImpl HashSpec Id) (publicKey : PublicKey) (message : Message) (signature : Signature) :
    OtsProbeSimulation.QueriesStable publicKey.parameter f (verifierFtsPrefix publicKey message signature) := by
  unfold verifierFtsPrefix
  apply (OtsProbeSimulation.queriesStable_messageDigest f publicKey.parameter publicKey.root message signature.randomness).bind
  split
  · exact OtsProbeSimulation.QueriesStable.pure _ _ _
  · exact (OtsProbeSimulation.queriesStable_ftsRecover f publicKey.parameter _ _ signature.ftsSecret signature.ftsPath).bind
      (OtsProbeSimulation.QueriesStable.pure _ _ _)

theorem verifierFtsPrefix_leaf_query_mem
    (f : QueryImpl HashSpec Id) (publicKey : PublicKey) (message : Message) (signature : Signature)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f (messageDigest publicKey.parameter publicKey.root message signature.randomness) = digest)
    (hadmissible : Admissible digest) (tree : FtsTree) :
    tweakableHashInput publicKey.parameter (.ftsLeaf (digestIndex digest) tree (digestLeaves digest (ftsIndexOf tree)))
      (digestBytes (signature.ftsSecret tree)) ∈ queriedInputs f (verifierFtsPrefix publicKey message signature) := by
  rw [verifierFtsPrefix, queriedInputs_bind]
  apply List.mem_append_right
  rw [hdigest]
  simp only [hadmissible, not_true_eq_false, if_false, queriedInputs_bind]
  apply List.mem_append_left
  exact ftsRecover_leaf_query_mem f publicKey.parameter (digestIndex digest) (digestLeaves digest) signature.ftsSecret signature.ftsPath tree

theorem liftHashSource_bind (computation : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    liftHashSource (computation >>= next) = liftHashSource computation >>= fun value => liftHashSource (next value) := by
  rw [liftHashSource, simulateQ_bind]
  rfl

theorem jointCappedVerifier_hit_revealed
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (message : Message) (signature : Signature)
    (next : Bool → OracleComp (OracleWorld + SigningSpec) α) (project : α → β) (q : Nat) (result : β)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (Option β × OtsProbeSimulation.SplitHashCache))
    (hbudget : q ≤ ftsFuel) (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (f : QueryImpl HashSpec Id) (hf : (mergedCache parameter table finalCache).AgreesWithFn f)
    (hvalue : entry.value.1 = some result)
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointComputation parameter root
          (Option.map project <$> OtsProbeSimulation.capOuterHashQueries
            (liftHashSource (verify (m := OracleComp HashSpec) ⟨root, parameter⟩ message signature) >>= next) q)
          context fuel history cache).run ftsCache)))
    (digest : MessageDigest) (tree : FtsTree)
    (hdigest : evalWithAnswerFn f (messageDigest parameter root message signature.randomness) = digest)
    (hadmissible : Admissible digest)
    (hsecret : signature.ftsSecret tree = table (digestIndex digest, tree, digestLeaves digest (ftsIndexOf tree))) :
    ∃ value, finalState.revealed (digestIndex digest, tree, digestLeaves digest (ftsIndexOf tree)) = some value := by
  rw [verify_eq_ftsPrefix, liftHashSource_bind, bind_assoc] at hresult
  have hqueries := hiddenHitsRevealed_maskedJointStablePrefix parameter root table
    (verifierFtsPrefix ⟨root, parameter⟩ message signature) _ project q result state finalState ftsFuel
    context fuel history cache ftsCache finalCache entry hbudget hclean hsynced f hf
    (queriesStable_verifierFtsPrefix f ⟨root, parameter⟩ message signature) hvalue hresult
  let probe : FtsSecretProbe := ⟨digestIndex digest, tree, digestLeaves digest (ftsIndexOf tree), signature.ftsSecret tree⟩
  exact hqueries (probe.input parameter)
    (verifierFtsPrefix_leaf_query_mem f ⟨root, parameter⟩ message signature digest hdigest hadmissible tree)
    probe (decodeProbe?_input parameter probe) hsecret.symm

end SphincsSecurity.Concrete.FtsProbeSimulation

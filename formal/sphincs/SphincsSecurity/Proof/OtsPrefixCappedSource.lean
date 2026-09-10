import SphincsSecurity.Proof.AdaptiveChainCap
import SphincsSecurity.Proof.OtsPrefixAccounting
import SphincsSecurity.Proof.OtsPrefixObservedBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

theorem prefixCappedSeedGame_contract (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (dummy : OtsReferenceWords) (adversary : Adversary) (selections : ReferenceFamily)
    (hselections : selections ∈ (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).support)
    (q : Nat) (hbound : HasHashQueryBound scheme adversary q) (hsmall : q < Fintype.card Digest) :
    let words := referenceFamilyWords selections dummy
    let segment : OtsPrefix := ⟨parameter, lay, tree, leaf, chainIdx, words lay tree leaf chainIdx⟩
    let inputs := canonicalGraphGameInputs adversary
    let hencoding := canonicalEncodingInputs_subset_gameInputs adversary parameter
    let hgraph := canonicalGraphInputs_subset_gameInputs adversary parameter
    ∀ (other : segment.ErasedSecrets) (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph),
      auxiliary ∈ (segment.referenceAuxSeedLaw inputs hencoding hgraph selections).support →
      let computation := fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary other.val ftsSecret words endpoint adversary
      let capped := fun endpoint => QueryCap.run PartialChainEndpoint.IsPrefixQuery (computation endpoint) q
      ((PartialChainEndpoint.realRun (fun _ => OtsPrefix.uniformImpl) capped (fun _ _ => none)).map
        (fun result => Option.map Prod.fst result.2.1) =
        (segment.seedObservedRun inputs hencoding hgraph auxiliary other.val ftsSecret words adversary).map
          (fun result => some result.2.1)) ∧
      ∀ result ∈ (PartialChainEndpoint.idealRun (fun _ => OtsPrefix.uniformImpl) capped (fun _ _ => none)).support,
        ∃ finished, result.2.1 = some finished ∧ finished.1.2.hashCalls ≤ q := by
  dsimp only
  intro other auxiliary hauxiliary
  let words := referenceFamilyWords selections dummy
  let segment : OtsPrefix := ⟨parameter, lay, tree, leaf, chainIdx, words lay tree leaf chainIdx⟩
  let inputs := canonicalGraphGameInputs adversary
  let hencoding := canonicalEncodingInputs_subset_gameInputs adversary parameter
  let hgraph := canonicalGraphInputs_subset_gameInputs adversary parameter
  let computation := fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary other.val ftsSecret words endpoint adversary
  let cost := fun result : Bool × SigningBoundaryTrace => result.2.hashCalls
  have hcharge : ∀ endpoint result, result ∈ support
      (QueryCap.counted PartialChainEndpoint.IsPrefixQuery (computation endpoint)) → result.2 ≤ cost result.1 :=
    fun endpoint result hresult => segment.seedGame_counted_le inputs hencoding hgraph auxiliary other.val
      ftsSecret words endpoint adversary result hresult
  have hreal : ∀ result ∈ (PartialChainEndpoint.realRun (fun _ => OtsPrefix.uniformImpl) computation (fun _ _ => none)).support,
      cost result.2.1 ≤ q :=
    prefixObservedRun_hashCalls_le parameter hparameter ftsSecret lay tree leaf chainIdx dummy adversary selections hselections
      q hbound other auxiliary hauxiliary
  exact ⟨PartialChainEndpoint.realRun_cap_erased _ computation cost q hcharge hreal,
    PartialChainEndpoint.idealRun_cap_valid _ computation cost q hcharge hreal hsmall⟩

end SphincsSecurity.Concrete

import SphincsSecurity.Proof.OtsProbeTerminal
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# One-time secret sampler transport

The lazy probe game samples full hash outputs at opaque chain-start coordinates. Truncating an
independent uniform table of those outputs gives exactly the concrete curried one-time secret
sampler. This finite coordinate type contains no structural `Position` and therefore does not
invoke its expensive `Fintype` enumeration.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

structure OtsSecretIndex where
  lay : Layer
  tree : TreeIndex
  leafIdx : LeafIndex
  chainIdx : ChainIndex
deriving Fintype, DecidableEq

def OtsSecretIndex.coordinate (index : OtsSecretIndex) : Coordinate :=
  .chainStart index.lay index.tree index.leafIdx index.chainIdx

theorem OtsSecretIndex.coordinate_injective :
    Function.Injective OtsSecretIndex.coordinate := by
  intro left right heq
  cases left
  cases right
  simpa [OtsSecretIndex.coordinate] using heq

def otsSecretTableEquiv :
    (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) ≃
      (OtsSecretIndex → Digest) where
  toFun secret index := secret index.lay index.tree index.leafIdx index.chainIdx
  invFun table lay tree leafIdx chainIdx := table ⟨lay, tree, leafIdx, chainIdx⟩
  left_inv secret := by rfl
  right_inv table := by
    funext index
    cases index
    rfl

def piProdEquiv (D A B : Type) : (D → A × B) ≃ (D → A) × (D → B) where
  toFun table := (fun index => (table index).1, fun index => (table index).2)
  invFun tables index := (tables.1 index, tables.2 index)
  left_inv table := by rfl
  right_inv tables := by rfl

noncomputable def splitOtsSecretTableEquiv :
    (OtsSecretIndex → HashOutput) ≃
      (OtsSecretIndex → Digest) ×
        (OtsSecretIndex → BitVec (hashOutputBits - digestBits)) :=
  (Equiv.piCongrRight fun _ => splitHashOutputEquiv digestBits (by decide)).trans
    (piProdEquiv OtsSecretIndex Digest (BitVec (hashOutputBits - digestBits)))

theorem splitOtsSecretTableEquiv_fst (table : OtsSecretIndex → HashOutput) :
    (splitOtsSecretTableEquiv table).1 = fun index => truncateHash (table index) := by
  rfl

theorem tableOtsSecret_eq_otsSecretTable
    (table : Coordinate → HashOutput) :
    tableOtsSecret table = otsSecretTableEquiv.symm
      (fun index => truncateHash (table index.coordinate)) := by
  rfl

set_option maxRecDepth 10000 in
theorem relTriple_sampleHashOutput_sampleDigest :
    RelTriple LazyRevealProbe.sampleHashOutput ($ᵗ Digest : ProbComp Digest)
      fun output digest => truncateHash output = digest := by
  let split := splitHashOutputEquiv digestBits (by decide)
  let pairSample :=
    ($ᵗ (Digest × BitVec (hashOutputBits - digestBits)) :
      ProbComp (Digest × BitVec (hashOutputBits - digestBits)))
  have hpair : RelTriple pairSample pairSample fun left right =>
      truncateHash (split.symm left) = right.1 := by
    apply relTriple_post_mono (relTriple_refl pairSample)
    intro left right heq
    subst right
    change (split (split.symm left)).1 = left.1
    rw [split.apply_symm_apply]
  have hmapped :
      RelTriple (split.symm <$> pairSample) (Prod.fst <$> pairSample)
        (fun output digest => truncateHash output = digest) :=
    relTriple_map
      (R := fun output digest => truncateHash output = digest) hpair
  have hleft :
      𝒟[split.symm <$> pairSample] = 𝒟[LazyRevealProbe.sampleHashOutput] := by
    rw [LazyRevealProbe.sampleHashOutput]
    exact evalDist_map_bijective_uniform_cross _ split.symm split.symm.bijective
  have hright :
      𝒟[Prod.fst <$> pairSample] = 𝒟[($ᵗ Digest : ProbComp Digest)] :=
    evalDist_map_fst_uniformSample_prod
  exact relTriple_of_evalDist_eq_right hright
    (relTriple_of_evalDist_eq_left hleft.symm hmapped)

noncomputable local instance sampleableOtsSecretTable :
    SampleableType (OtsSecretIndex → Digest) :=
  SampleableType.ofFintype (OtsSecretIndex → Digest)

noncomputable local instance sampleableOtsHashTable :
    SampleableType (OtsSecretIndex → HashOutput) :=
  SampleableType.ofFintype (OtsSecretIndex → HashOutput)

noncomputable local instance sampleableOtsHighTable :
    SampleableType (OtsSecretIndex → BitVec (hashOutputBits - digestBits)) :=
  SampleableType.ofFintype
    (OtsSecretIndex → BitVec (hashOutputBits - digestBits))

noncomputable local instance sampleableSplitOtsTable :
    SampleableType
      ((OtsSecretIndex → Digest) ×
        (OtsSecretIndex → BitVec (hashOutputBits - digestBits))) :=
  SampleableType.ofFintype _

noncomputable local instance sampleableOtsSecrets :
    SampleableType (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  otsSecretsSampleableType

attribute [local semireducible] sampleOtsSecrets

theorem evalDist_sampleOtsSecrets_uncurry :
    𝒟[otsSecretTableEquiv <$> sampleOtsSecrets] =
      𝒟[($ᵗ (OtsSecretIndex → Digest) : ProbComp (OtsSecretIndex → Digest))] := by
  rw [show sampleOtsSecrets =
      ($ᵗ (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :
        ProbComp (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)) by rfl]
  exact evalDist_map_bijective_uniform_cross _ otsSecretTableEquiv
    otsSecretTableEquiv.bijective

set_option maxRecDepth 10000 in
theorem evalDist_lazyOtsSecrets_eq_sampled
    (computation : OracleComp (OtsSecretIndex →ₒ Digest) alpha) :
    𝒟[(simulateQ
        (randomOracle : QueryImpl (OtsSecretIndex →ₒ Digest)
          (StateT (QueryCache (OtsSecretIndex →ₒ Digest)) ProbComp))
        computation).run' (∅ : QueryCache (OtsSecretIndex →ₒ Digest))] =
      𝒟[do
        let secret ← sampleOtsSecrets
        pure (evalWithAnswerFn
          (QueryImpl.ofFn (spec := OtsSecretIndex →ₒ Digest)
            (otsSecretTableEquiv secret)) computation)] := by
  let evaluate := fun table : OtsSecretIndex → Digest =>
    evalWithAnswerFn (QueryImpl.ofFn (spec := OtsSecretIndex →ₒ Digest) table)
      computation
  calc
    _ = 𝒟[evaluate <$>
        ($ᵗ (OtsSecretIndex → Digest) : ProbComp (OtsSecretIndex → Digest))] := by
      simpa [evaluate, bind_pure_comp] using
        (OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable computation)
    _ = 𝒟[evaluate <$> (otsSecretTableEquiv <$> sampleOtsSecrets)] := by
      rw [evalDist_map, evalDist_map]
      exact congrArg (Functor.map evaluate) evalDist_sampleOtsSecrets_uncurry.symm
    _ = _ := by
      simp [evaluate, Functor.map_map]

set_option maxRecDepth 10000 in
theorem evalDist_uniformOtsHashTable_truncate :
    𝒟[(fun table : OtsSecretIndex → HashOutput =>
          otsSecretTableEquiv.symm (fun index => truncateHash (table index))) <$>
        ($ᵗ (OtsSecretIndex → HashOutput) : ProbComp (OtsSecretIndex → HashOutput))] =
      𝒟[sampleOtsSecrets] := by
  let split := splitOtsSecretTableEquiv
  have hsplit :
      𝒟[split <$> ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))] =
        𝒟[($ᵗ ((OtsSecretIndex → Digest) ×
          (OtsSecretIndex → BitVec (hashOutputBits - digestBits))) :
            ProbComp ((OtsSecretIndex → Digest) ×
              (OtsSecretIndex → BitVec (hashOutputBits - digestBits))))] :=
    evalDist_map_bijective_uniform_cross _ split split.bijective
  have hfst :
      𝒟[Prod.fst <$> ($ᵗ ((OtsSecretIndex → Digest) ×
          (OtsSecretIndex → BitVec (hashOutputBits - digestBits))) :
            ProbComp ((OtsSecretIndex → Digest) ×
              (OtsSecretIndex → BitVec (hashOutputBits - digestBits))))] =
        𝒟[($ᵗ (OtsSecretIndex → Digest) : ProbComp (OtsSecretIndex → Digest))] :=
    evalDist_map_fst_uniformSample_prod
  have hcurried :
      𝒟[otsSecretTableEquiv.symm <$>
          ($ᵗ (OtsSecretIndex → Digest) : ProbComp (OtsSecretIndex → Digest))] =
        𝒟[($ᵗ (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :
          ProbComp (Layer → TreeIndex → LeafIndex → ChainIndex → Digest))] :=
    evalDist_map_bijective_uniform_cross _ otsSecretTableEquiv.symm
      otsSecretTableEquiv.symm.bijective
  have hmapper :
      (fun table : OtsSecretIndex → HashOutput =>
        otsSecretTableEquiv.symm (fun index => truncateHash (table index))) =
      (fun table : OtsSecretIndex → HashOutput =>
        otsSecretTableEquiv.symm (Prod.fst (split table))) := by
    funext table
    rw [splitOtsSecretTableEquiv_fst]
  have hcomputation :
      (fun table : OtsSecretIndex → HashOutput =>
          otsSecretTableEquiv.symm (fun index => truncateHash (table index))) <$>
        ($ᵗ (OtsSecretIndex → HashOutput) : ProbComp (OtsSecretIndex → HashOutput)) =
      otsSecretTableEquiv.symm <$> (Prod.fst <$> (split <$>
        ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput)))) := by
    simp only [Functor.map_map]
    rw [hmapper]
  calc
    _ = 𝒟[otsSecretTableEquiv.symm <$> (Prod.fst <$> (split <$>
          ($ᵗ (OtsSecretIndex → HashOutput) :
            ProbComp (OtsSecretIndex → HashOutput))))] := congrArg evalDist hcomputation
    _ = 𝒟[otsSecretTableEquiv.symm <$> (Prod.fst <$>
          ($ᵗ ((OtsSecretIndex → Digest) ×
            (OtsSecretIndex → BitVec (hashOutputBits - digestBits))) :
              ProbComp ((OtsSecretIndex → Digest) ×
                (OtsSecretIndex → BitVec (hashOutputBits - digestBits)))))] := by
      rw [evalDist_map, evalDist_map, hsplit, ← evalDist_map, ← evalDist_map]
    _ = 𝒟[otsSecretTableEquiv.symm <$>
          ($ᵗ (OtsSecretIndex → Digest) : ProbComp (OtsSecretIndex → Digest))] := by
      rw [evalDist_map, hfst, ← evalDist_map]
    _ = 𝒟[($ᵗ (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :
          ProbComp (Layer → TreeIndex → LeafIndex → ChainIndex → Digest))] := hcurried
    _ = 𝒟[sampleOtsSecrets] := by rfl

end SphincsSecurity.Concrete.OtsProbeSimulation

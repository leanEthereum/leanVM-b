import XmssSecurity.Proof.ChainTableUniformity
import XmssSecurity.Proof.ChainQueryPresence
import XmssSecurity.Proof.AdaptiveFreshTarget
import XmssSecurity.Proof.RandomOraclePresampling
import XmssSecurity.Proof.HiddenValue

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

abbrev ChainEdgeIndex := Epoch × ChainStep

def chainTableEdgeInput
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) (edge : ChainEdgeIndex) : HashInput :=
  Concrete.CacheView.chainInput parameter edge.1 chain edge.2
    (table (edge.1, chainStepDigit edge.2))

def chainStepNextDigit (step : ChainStep) : Digit :=
  ⟨step.val + 1, by
    have hstep := step.isLt
    omega⟩

def chainTableEdgeTarget
    (table : ChainValueIndex → Digest) (edge : ChainEdgeIndex) : Digest :=
  table (edge.1, chainStepNextDigit edge.2)

def ChainTableSeedsMatch
    (secretKey : SecretKey) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) : Prop :=
  ∀ epoch, secretKey.chainStart epoch chain = table (epoch, ⟨0, by simp [chainLength]⟩)

def ChainTableEdgesMatch
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (chain : ChainIndex) (table : ChainValueIndex → Digest) : Prop :=
  ∀ edge, ∃ output,
    cache (chainTableEdgeInput parameter chain table edge) = some output ∧
      truncateHash output = chainTableEdgeTarget table edge

theorem ChainTableEdgesMatch.mono
    {cache larger : QueryCache HashSpec} {parameter : PublicParameter}
    {chain : ChainIndex} {table : ChainValueIndex → Digest}
    (hmatch : ChainTableEdgesMatch cache parameter chain table)
    (hle : cache ≤ larger) :
    ChainTableEdgesMatch larger parameter chain table := by
  intro edge
  obtain ⟨output, hcached, htarget⟩ := hmatch edge
  exact ⟨output, hle hcached, htarget⟩

noncomputable local instance presamplingSampleableChainEdges :
    SampleableType (ChainEdgeIndex → Digest) :=
  SampleableType.ofFintype (ChainEdgeIndex → Digest)

abbrev FlatSecret := Epoch × ChainIndex → Digest

noncomputable local instance presamplingSampleableFlatSecret :
    SampleableType FlatSecret :=
  SampleableType.ofFintype FlatSecret

noncomputable local instance presamplingSampleableSecret :
    SampleableType (Epoch → ChainIndex → Digest) :=
  SampleableType.ofFintype (Epoch → ChainIndex → Digest)

def unflattenSecret (table : FlatSecret) :
    Epoch → ChainIndex → Digest := fun epoch chain => table (epoch, chain)

def flatSecretEquiv :
    (Epoch → ChainIndex → Digest) ≃ FlatSecret where
  toFun secret index := secret index.1 index.2
  invFun := unflattenSecret
  left_inv secret := by
    funext epoch chain
    rfl
  right_inv table := by
    funext index
    rfl

noncomputable def extractFixedChainSeeds
    (chain : ChainIndex) : List Epoch →
      ProbComp (List Digest × FlatSecret)
  | [] => do
      let table ← $ᵗ FlatSecret
      return ([], table)
  | epoch :: epochs => do
      let value ← $ᵗ Digest
      let rest ← extractFixedChainSeeds chain epochs
      return (value :: rest.1,
        Function.update rest.2 (epoch, chain) value)

@[simp]
theorem extractFixedChainSeeds_nil (chain : ChainIndex) :
    extractFixedChainSeeds chain [] = do
      let table ← $ᵗ FlatSecret
      return ([], table) := rfl

theorem extractFixedChainSeeds_cons
    (chain : ChainIndex) (epoch : Epoch) (epochs : List Epoch) :
    extractFixedChainSeeds chain (epoch :: epochs) = do
      let value ← $ᵗ Digest
      let rest ← extractFixedChainSeeds chain epochs
      return (value :: rest.1,
        Function.update rest.2 (epoch, chain) value) := rfl

def fixedChainSeedView (chain : ChainIndex) (epochs : List Epoch)
    (table : FlatSecret) : List Digest × FlatSecret :=
  (epochs.map (fun target => table (target, chain)), table)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
/-- Exposing the selected chain's seed tape and patching it back into a uniform flat secret preserves the joint distribution of the tape read from that secret. -/
theorem evalDist_extractFixedChainSeeds_eq_uniform
    (chain : ChainIndex) :
    ∀ (epochs : List Epoch), epochs.Nodup →
      𝒟[extractFixedChainSeeds chain epochs] =
      𝒟[fixedChainSeedView chain epochs <$> ($ᵗ FlatSecret)] := by
  intro epochs
  induction epochs with
  | nil =>
      intro _hnodup
      simp only [extractFixedChainSeeds_nil, map_eq_bind_pure_comp,
        bind_pure_comp]
      congr 2
  | cons epoch epochs ih =>
      intro hnodup
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      have htailUpdate (table : FlatSecret) (value : Digest) :
          epochs.map (fun target =>
              Function.update table (epoch, chain) value (target, chain)) =
            epochs.map (fun target => table (target, chain)) := by
        apply List.map_congr_left
        intro target htarget
        rw [Function.update_of_ne]
        intro heq
        have htargetEpoch : target = epoch := congrArg Prod.fst heq
        subst target
        exact hnotMem htarget
      rw [extractFixedChainSeeds_cons]
      calc
        𝒟[$ᵗ Digest >>= fun value =>
            extractFixedChainSeeds chain epochs >>= fun rest =>
              pure (value :: rest.1,
                Function.update rest.2 (epoch, chain) value)] =
            𝒟[$ᵗ Digest >>= fun value =>
              (fixedChainSeedView chain epochs <$> ($ᵗ FlatSecret)) >>=
                  fun rest => pure (value :: rest.1,
                    Function.update rest.2 (epoch, chain) value)] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro value
          conv_lhs => rw [evalDist_bind]
          conv_rhs => rw [evalDist_bind]
          rw [ih htailNodup]
        _ = 𝒟[$ᵗ Digest >>= fun value =>
              $ᵗ FlatSecret >>= fun table =>
                pure (value :: epochs.map (fun target => table (target, chain)),
                  Function.update table (epoch, chain) value)] := by
          simp [fixedChainSeedView]
        _ = 𝒟[$ᵗ Digest >>= fun value =>
              $ᵗ FlatSecret >>= fun table =>
                pure ((fun updated : FlatSecret =>
                  ((epoch :: epochs).map
                    (fun target => updated (target, chain)), updated))
                  (Function.update table (epoch, chain) value))] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro value
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro table
          simp [htailUpdate table value]
        _ = 𝒟[fixedChainSeedView chain (epoch :: epochs) <$>
              ($ᵗ FlatSecret)] :=
          OracleComp.evalDist_uniformSample_bind_update_map
            (R := Digest) (epoch, chain)
            (fixedChainSeedView chain (epoch :: epochs))

theorem evalDist_map_truncate_drawList (count : Nat) :
    𝒟[List.map truncateHash <$>
      OracleComp.drawList ($ᵗ HashOutput) count] =
      𝒟[OracleComp.drawList ($ᵗ Digest) count] := by
  induction count with
  | zero => simp [OracleComp.drawList]
  | succ count ih =>
      simp only [OracleComp.drawList, map_eq_bind_pure_comp, bind_assoc,
        pure_bind, Function.comp_apply, List.map_cons]
      calc
        𝒟[$ᵗ HashOutput >>= fun output =>
            OracleComp.drawList ($ᵗ HashOutput) count >>= fun outputs =>
              pure (truncateHash output :: outputs.map truncateHash)] =
            𝒟[(truncateHash <$> ($ᵗ HashOutput)) >>= fun output =>
              (List.map truncateHash <$>
                OracleComp.drawList ($ᵗ HashOutput) count) >>= fun outputs =>
                pure (output :: outputs)] := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = 𝒟[$ᵗ Digest >>= fun output =>
              (List.map truncateHash <$>
                OracleComp.drawList ($ᵗ HashOutput) count) >>= fun outputs =>
                pure (output :: outputs)] := by
          conv_lhs => rw [evalDist_bind]
          conv_rhs => rw [evalDist_bind]
          rw [Rom.evalDist_truncate_uniformHashOutput]
        _ = 𝒟[$ᵗ Digest >>= fun output =>
              OracleComp.drawList ($ᵗ Digest) count >>= fun outputs =>
                pure (output :: outputs)] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro output
          conv_lhs => rw [evalDist_bind]
          conv_rhs => rw [evalDist_bind]
          rw [ih]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 1000000 in
theorem drawList_truncate_probability (targets : List Digest) :
    Pr[fun outputs : List HashOutput => outputs.map truncateHash = targets |
      OracleComp.drawList ($ᵗ HashOutput) targets.length] =
      ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ targets.length) := by
  induction targets with
  | nil => simp [OracleComp.drawList]
  | cons target targets ih =>
      rw [List.length_cons, OracleComp.drawList, probEvent_bind_eq_tsum]
      let tailProbability : ℝ≥0∞ :=
        ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ targets.length)
      calc
        (∑' output : HashOutput, Pr[= output | $ᵗ HashOutput] *
            Pr[fun outputs : List HashOutput => outputs.map truncateHash = target :: targets |
              do
                let rest ← OracleComp.drawList ($ᵗ HashOutput) targets.length
                pure (output :: rest)]) =
            ∑' output : HashOutput, Pr[= output | $ᵗ HashOutput] *
              (if truncateHash output = target then tailProbability else 0) := by
          apply tsum_congr
          intro output
          congr 1
          rw [bind_pure_comp, probEvent_map]
          by_cases htarget : truncateHash output = target
          · rw [if_pos htarget]
            change Pr[fun rest : List HashOutput =>
              truncateHash output :: rest.map truncateHash = target :: targets |
                OracleComp.drawList ($ᵗ HashOutput) targets.length] = tailProbability
            simpa [htarget, tailProbability] using ih
          · rw [if_neg htarget]
            apply probEvent_eq_zero
            intro rest _ heq
            exact htarget (List.cons.inj heq).1
        _ = (∑' output : HashOutput,
              if truncateHash output = target then
                Pr[= output | $ᵗ HashOutput] else 0) * tailProbability := by
          rw [← ENNReal.tsum_mul_right]
          apply tsum_congr
          intro output
          by_cases htarget : truncateHash output = target <;> simp [htarget]
        _ = Pr[fun output : HashOutput => truncateHash output = target |
              $ᵗ HashOutput] * tailProbability := by
          rw [probEvent_eq_tsum_ite]
        _ = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ * tailProbability := by
          rw [Rom.uniform_truncate_probability]
        _ = ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^
          (target :: targets).length) := by
          simp [tailProbability, pow_succ, mul_comm]

theorem drawList_support_length
    {Value : Type} (draw : ProbComp Value) :
    ∀ (count : Nat) (values : List Value),
      values ∈ support (OracleComp.drawList draw count) →
      values.length = count := by
  intro count
  induction count with
  | zero =>
      intro values hvalues
      simp only [OracleComp.drawList, support_pure,
        Set.mem_singleton_iff] at hvalues
      subst values
      rfl
  | succ count ih =>
      intro values hvalues
      rw [OracleComp.drawList, mem_support_bind_iff] at hvalues
      obtain ⟨value, _hvalue, hrest⟩ := hvalues
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst values
      simp [ih rest hrest]

theorem drawList_digest_probability (targets : List Digest) :
    Pr[= targets |
      OracleComp.drawList ($ᵗ Digest) targets.length] =
      ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ targets.length) := by
  calc
    Pr[= targets | OracleComp.drawList ($ᵗ Digest) targets.length] =
        Pr[= targets | List.map truncateHash <$>
          OracleComp.drawList ($ᵗ HashOutput) targets.length] :=
      probOutput_congr rfl
        (evalDist_map_truncate_drawList targets.length).symm
    _ = Pr[fun outputs : List HashOutput =>
          outputs.map truncateHash = targets |
        OracleComp.drawList ($ᵗ HashOutput) targets.length] := by
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      rfl
    _ = ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ targets.length) :=
      drawList_truncate_probability targets

theorem evalDist_listOfFn_uniform_eq_drawList (count : Nat) :
    𝒟[List.ofFn <$> ($ᵗ (Fin count → Digest))] =
      𝒟[OracleComp.drawList ($ᵗ Digest) count] := by
  apply SPMF.ext
  intro target
  change Pr[= target | List.ofFn <$> ($ᵗ (Fin count → Digest))] =
    Pr[= target | OracleComp.drawList ($ᵗ Digest) count]
  by_cases hlength : target.length = count
  · let targetFunction : Fin count → Digest := fun index =>
      target.get (Fin.cast hlength.symm index)
    have hofFn : List.ofFn targetFunction = target := by
      calc
        List.ofFn targetFunction = List.ofFn (List.get target) := by
          exact List.ofFn_congr hlength (List.get target) |>.symm
        _ = target := List.ofFn_get target
    calc
      Pr[= target | List.ofFn <$> ($ᵗ (Fin count → Digest))] =
          Pr[= targetFunction | $ᵗ (Fin count → Digest)] := by
        rw [← hofFn, probOutput_map_injective _ List.ofFn_injective]
      _ = ((((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ^ count) := by
        rw [probOutput_uniformSample, Fintype.card_fun, Fintype.card_fin,
          HiddenValue.card_digest, Nat.cast_pow, ENNReal.inv_pow]
      _ = Pr[= target |
          OracleComp.drawList ($ᵗ Digest) count] := by
        rw [← hlength]
        exact (drawList_digest_probability target).symm
  · have hleft : Pr[= target |
        List.ofFn <$> ($ᵗ (Fin count → Digest))] = 0 := by
      apply probOutput_eq_zero_of_not_mem_support
      intro htarget
      rw [support_map] at htarget
      obtain ⟨values, _hvalues, heq⟩ := htarget
      apply hlength
      rw [← heq]
      simp
    have hright : Pr[= target |
        OracleComp.drawList ($ᵗ Digest) count] = 0 := by
      apply probOutput_eq_zero_of_not_mem_support
      intro htarget
      exact hlength
        (drawList_support_length ($ᵗ Digest) count target htarget)
    rw [hleft, hright]

structure ProgrammedFixedChainKeygenView where
  publicKey : PublicKey
  secretKey : SecretKey
  cache : QueryCache HashSpec
  table : ChainValueIndex → Digest

noncomputable def actualFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
  return {
    publicKey := keyResult.1.1
    secretKey := keyResult.1.2
    cache := keyResult.2
    table := keygenChainValueTable keyResult.2 keyResult.1.2 chain
  }

noncomputable def explicitFixedChainKeygenFromSecret
    (parameter : PublicParameter) (chain : ChainIndex)
    (secret : Epoch → ChainIndex → Digest) :
    ProbComp ProgrammedFixedChainKeygenView := do
  let rootResult ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)).run ∅
  return {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey := (SecretKey.withoutPrecomputation parameter secret)
    cache := rootResult.2
    table := keygenChainValueTable rootResult.2 (SecretKey.withoutPrecomputation parameter secret) chain
  }

noncomputable def explicitFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let secret ← Concrete.sampleSecret
  explicitFixedChainKeygenFromSecret parameter chain secret

theorem evalDist_actualFixedChainKeygen_eq_explicit
    (chain : ChainIndex) :
    evalDist (actualFixedChainKeygen chain) =
      evalDist (explicitFixedChainKeygen chain) := by
  unfold actualFixedChainKeygen explicitFixedChainKeygen
    explicitFixedChainKeygenFromSecret Concrete.keygen
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, bind_assoc, pure_bind]
  have hparameter :
      (simulateQ xmssRomImpl
        (liftM Concrete.samplePublicParameter)).run ∅ =
        (fun parameter => (parameter, ∅)) <$>
          Concrete.samplePublicParameter := by
    simpa only [xmssRomImpl] using
      (roSim.run_liftM
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp))
        Concrete.samplePublicParameter ∅)
  rw [hparameter]
  simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  have hsecret :
      (simulateQ xmssRomImpl (liftM Concrete.sampleSecret)).run ∅ =
        (fun secret => (secret, ∅)) <$> Concrete.sampleSecret := by
    simpa only [xmssRomImpl] using
      (roSim.run_liftM
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp))
        Concrete.sampleSecret ∅)
  rw [hsecret]
  simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secret
  have htree :
      simulateQ xmssRomImpl
          (liftM (Concrete.treeNode parameter secret treeHeight
            Concrete.rootNode : OracleComp HashSpec Digest)) =
        simulateQ
          (randomOracle : QueryImpl HashSpec
            (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest) := by
    simp only [xmssRomImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)
  rw [htree]

set_option maxRecDepth 100000 in
theorem evalDist_unflatten_uniformFlatSecret_eq_sampleSecret :
    evalDist (unflattenSecret <$> ($ᵗ FlatSecret)) =
      evalDist Concrete.sampleSecret := by
  unfold Concrete.sampleSecret
  exact evalDist_map_bijective_uniform_cross
    (α := FlatSecret) (β := Epoch → ChainIndex → Digest)
    (fun table : FlatSecret => unflattenSecret table)
    flatSecretEquiv.symm.bijective

noncomputable def flatExplicitFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let flatSecret ← $ᵗ FlatSecret
  explicitFixedChainKeygenFromSecret parameter chain
    (unflattenSecret flatSecret)

theorem evalDist_explicitFixedChainKeygen_eq_flat
    (chain : ChainIndex) :
    evalDist (explicitFixedChainKeygen chain) =
      evalDist (flatExplicitFixedChainKeygen chain) := by
  unfold explicitFixedChainKeygen flatExplicitFixedChainKeygen
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  calc
    evalDist (Concrete.sampleSecret >>= fun secret =>
        explicitFixedChainKeygenFromSecret parameter chain secret) =
        evalDist ((unflattenSecret <$> ($ᵗ FlatSecret)) >>= fun secret =>
          explicitFixedChainKeygenFromSecret parameter chain secret) := by
      conv_lhs => rw [evalDist_bind]
      conv_rhs => rw [evalDist_bind]
      rw [evalDist_unflatten_uniformFlatSecret_eq_sampleSecret]
    _ = evalDist (($ᵗ FlatSecret) >>= fun flatSecret =>
          explicitFixedChainKeygenFromSecret parameter chain
            (unflattenSecret flatSecret)) := by
      simp [map_eq_bind_pure_comp, bind_assoc]

noncomputable def extractedExplicitFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let secretView ← extractFixedChainSeeds chain allEpochs
  explicitFixedChainKeygenFromSecret parameter chain
    (unflattenSecret secretView.2)

theorem evalDist_flatExplicitFixedChainKeygen_eq_extracted
    (chain : ChainIndex) :
    evalDist (flatExplicitFixedChainKeygen chain) =
      evalDist (extractedExplicitFixedChainKeygen chain) := by
  unfold flatExplicitFixedChainKeygen extractedExplicitFixedChainKeygen
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  symm
  calc
    evalDist (extractFixedChainSeeds chain allEpochs >>= fun secretView =>
        explicitFixedChainKeygenFromSecret parameter chain
          (unflattenSecret secretView.2)) =
        evalDist ((fixedChainSeedView chain allEpochs <$>
          ($ᵗ FlatSecret)) >>= fun secretView =>
            explicitFixedChainKeygenFromSecret parameter chain
              (unflattenSecret secretView.2)) := by
      conv_lhs => rw [evalDist_bind]
      conv_rhs => rw [evalDist_bind]
      rw [evalDist_extractFixedChainSeeds_eq_uniform chain allEpochs allEpochs_nodup]
    _ = evalDist (($ᵗ FlatSecret) >>= fun flatSecret =>
          explicitFixedChainKeygenFromSecret parameter chain
            (unflattenSecret flatSecret)) := by
      simp [map_eq_bind_pure_comp, bind_assoc, fixedChainSeedView]

theorem evalDist_actualFixedChainKeygen_eq_extracted
    (chain : ChainIndex) :
    evalDist (actualFixedChainKeygen chain) =
      evalDist (extractedExplicitFixedChainKeygen chain) :=
  (evalDist_actualFixedChainKeygen_eq_explicit chain).trans
    ((evalDist_explicitFixedChainKeygen_eq_flat chain).trans
      (evalDist_flatExplicitFixedChainKeygen_eq_extracted chain))

theorem keygenChainValueTable_seedsMatch
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (chain : ChainIndex) :
    ChainTableSeedsMatch secretKey chain
      (keygenChainValueTable cache secretKey chain) := by
  intro epoch
  simp [keygenChainValueTable]

set_option maxRecDepth 10000 in
theorem Concrete.keygenChainValueTable_edgesMatch
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (chain : ChainIndex) :
    ChainTableEdgesMatch keyResult.2 keyResult.1.2.parameter chain
      (keygenChainValueTable keyResult.2 keyResult.1.2 chain) := by
  intro edge
  let nextDigit := chainStepNextDigit edge.2
  have hpositive : 0 < nextDigit.val := by
    simp [nextDigit, chainStepNextDigit]
  obtain ⟨previous, output, hprevious, hcached, houtput⟩ :=
    Concrete.keygen_cache_has_chainValue_preimage keyResult hkeygen edge.1 chain
      nextDigit hpositive
  have hstep : previous = edge.2 := by
    apply Fin.ext
    dsimp only [nextDigit, chainStepNextDigit] at hprevious
    omega
  subst previous
  refine ⟨output, ?_, ?_⟩
  · simpa [chainTableEdgeInput, keygenChainValueTable, chainStepDigit] using hcached
  · simpa [chainTableEdgeTarget, keygenChainValueTable, nextDigit,
      Wots.signChain] using houtput

theorem Concrete.CacheReplay.rootTree_chain_query_cached_from_cache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (step : ChainStep)
    (initialCache : QueryCache HashSpec)
    (result : Digest × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run initialCache)) :
    ∃ output, result.2
      (Concrete.CacheView.chainInput parameter epoch chain step
        (Wots.walk
          (Concrete.CacheView.chainStep result.2 parameter epoch chain)
          0 step.val (secret epoch chain))) = some output := by
  apply Concrete.CacheReplay.treeNode_chain_query_cached_in_largerCache
    parameter secret epoch chain step treeHeight Concrete.rootNode le_rfl
  · unfold TreeSubtreeValid Concrete.rootNode lifetime
    norm_num
  · unfold TreeCovers Concrete.rootNode
    constructor
    · simp
    · simp [lifetime]
  · exact hresult
  · exact le_rfl

theorem evalDist_rootTree_run_eq_chainHash_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (steps : Nat)
    (previous : Digest)
    (initialCache prefixCache : QueryCache HashSpec)
    (hvalid : steps < chainLength - 1)
    (hprefix : (previous, prefixCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch chain 0 steps
          (secret epoch chain) :
          OracleComp HashSpec Digest)).run initialCache)) :
    evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run prefixCache) =
      evalDist ((simulateQ randomOracle
        (Concrete.chainHash parameter epoch chain
          ⟨steps, hvalid⟩ previous : OracleComp HashSpec Digest)).run
            prefixCache >>= fun hashResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run hashResult.2) := by
  let target := Concrete.CacheView.chainInput parameter epoch chain
    ⟨steps, hvalid⟩ previous
  have hcached : ∀ result ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run prefixCache),
      ∃ output, result.2 target = some output := by
    intro result hresult
    have hprefixLe := Concrete.CacheReplay.randomOracle_cache_le
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest) prefixCache result hresult
    have hreplay := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
      (Concrete.chainWalk parameter epoch chain 0 steps
        (secret epoch chain) :
        OracleComp HashSpec Digest)
      initialCache prefixCache result.2 previous hprefix hprefixLe
    rw [Concrete.CacheReplay.eval_chainWalk] at hreplay
    obtain ⟨output, houtput⟩ :=
      Concrete.CacheReplay.rootTree_chain_query_cached_from_cache
        parameter secret epoch chain ⟨steps, hvalid⟩
        prefixCache result hresult
    refine ⟨output, ?_⟩
    change result.2
      (Concrete.CacheView.chainInput parameter epoch chain
        ⟨steps, hvalid⟩ previous) = some output
    rw [← hreplay]
    exact houtput
  calc
    evalDist ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run prefixCache) =
        evalDist ((randomOracle (spec := HashSpec) target).run prefixCache >>=
          fun queryResult =>
            (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run queryResult.2) :=
      OracleComp.evalDist_randomOracle_run_eq_query_then_of_cached
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest) prefixCache target hcached
    _ = evalDist ((simulateQ randomOracle
          (Concrete.chainHash parameter epoch chain
            ⟨steps, hvalid⟩ previous :
              OracleComp HashSpec Digest)).run prefixCache >>= fun hashResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run hashResult.2) := by
      simp [Concrete.chainHash, Concrete.tweakableHash, Concrete.oracleHash,
        target, Concrete.CacheView.chainInput]

theorem evalDist_rootTree_run_eq_chainWalk_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1)
    (initialCache : QueryCache HashSpec) :
    evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache) =
      evalDist ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch chain 0 steps
          (secret epoch chain) : OracleComp HashSpec Digest)).run initialCache >>=
            fun chainResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run chainResult.2) := by
  induction steps generalizing initialCache with
  | zero =>
      simp [Concrete.chainWalk]
  | succ steps ih =>
      have hvalid : steps < chainLength - 1 := by omega
      calc
        evalDist ((simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run initialCache) =
            evalDist ((simulateQ randomOracle
              (Concrete.chainWalk parameter epoch chain 0 steps
                (secret epoch chain) : OracleComp HashSpec Digest)).run
                  initialCache >>= fun prefixResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run prefixResult.2) :=
          ih (by omega) initialCache
        _ = evalDist ((simulateQ randomOracle
              (Concrete.chainWalk parameter epoch chain 0 steps
                (secret epoch chain) : OracleComp HashSpec Digest)).run
                  initialCache >>= fun prefixResult =>
              (simulateQ randomOracle
                (Concrete.chainHash parameter epoch chain ⟨steps, hvalid⟩
                  prefixResult.1 : OracleComp HashSpec Digest)).run
                    prefixResult.2 >>= fun hashResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run hashResult.2) := by
          apply evalDist_bind_congr
          intro prefixResult hprefix
          exact evalDist_rootTree_run_eq_chainHash_then_rootTree
            parameter secret epoch chain steps prefixResult.1 initialCache
            prefixResult.2 hvalid hprefix
        _ = evalDist ((simulateQ randomOracle
              (Concrete.chainWalk parameter epoch chain 0 (steps + 1)
                (secret epoch chain) : OracleComp HashSpec Digest)).run
                  initialCache >>= fun chainResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run chainResult.2) := by
          rw [Concrete.chainWalk, simulateQ_bind, StateT.run_bind]
          simp only [zero_add]
          simp only [hvalid, ↓reduceDIte, bind_assoc]

theorem Concrete.chainTrajectory_back_map_eq_chainWalk
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    Vector.back <$> Concrete.chainTrajectory parameter epoch chain position steps value =
      (Concrete.chainWalk parameter epoch chain position steps value :
        OracleComp HashSpec Digest) := by
  induction steps with
  | zero =>
      rw [Concrete.chainTrajectory_zero]
      simp only [map_pure, Concrete.chainWalk]
      simp [Vector.back_ofFn]
  | succ steps ih =>
      calc
        Vector.back <$>
            Concrete.chainTrajectory parameter epoch chain position
              (steps + 1) value =
            (Vector.back <$> Concrete.chainTrajectory parameter epoch chain
              position steps value) >>= fun previous =>
              if hvalid : position + steps < chainLength - 1 then
                Concrete.chainHash parameter epoch chain
                  ⟨position + steps, hvalid⟩ previous
              else pure 0 := by
          rw [Concrete.chainTrajectory_succ]
          by_cases hvalid : position + steps < chainLength - 1
          · simp [hvalid, map_eq_bind_pure_comp, bind_assoc]
          · simp [hvalid, map_eq_bind_pure_comp, bind_assoc]
        _ = Concrete.chainWalk parameter epoch chain position
            (steps + 1) value := by
          rw [ih]
          rfl

theorem evalDist_chainTrajectory_run_cache_eq_chainWalk_run_cache
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (value : Digest)
    (initialCache : QueryCache HashSpec) :
    evalDist ((fun result : Vector Digest (steps + 1) × QueryCache HashSpec =>
      (result.1.back, result.2)) <$>
        (simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain position steps value)).run
            initialCache) =
      evalDist ((simulateQ randomOracle
        (Concrete.chainWalk parameter epoch chain position steps value :
          OracleComp HashSpec Digest)).run initialCache) := by
  rw [← StateT.run_map]
  rw [← simulateQ_map]
  rw [Concrete.chainTrajectory_back_map_eq_chainWalk]

theorem evalDist_rootTree_run_eq_chainTrajectory_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1)
    (initialCache : QueryCache HashSpec) :
    evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache) =
      evalDist ((simulateQ randomOracle
        (Concrete.chainTrajectory parameter epoch chain 0 steps
          (secret epoch chain))).run initialCache >>= fun trajectoryResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run trajectoryResult.2) := by
  calc
    evalDist ((simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run initialCache) =
        evalDist ((simulateQ randomOracle
          (Concrete.chainWalk parameter epoch chain 0 steps
            (secret epoch chain) : OracleComp HashSpec Digest)).run initialCache >>=
              fun chainResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run chainResult.2) :=
      evalDist_rootTree_run_eq_chainWalk_then_rootTree parameter secret epoch
        chain steps hsteps initialCache
    _ = evalDist (((fun result : Vector Digest (steps + 1) × QueryCache HashSpec =>
          (result.1.back, result.2)) <$>
            (simulateQ randomOracle
              (Concrete.chainTrajectory parameter epoch chain 0 steps
                (secret epoch chain))).run initialCache) >>= fun chainResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run chainResult.2) := by
      conv_lhs => rw [evalDist_bind]
      conv_rhs => rw [evalDist_bind]
      rw [evalDist_chainTrajectory_run_cache_eq_chainWalk_run_cache]
    _ = evalDist ((simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain 0 steps
            (secret epoch chain))).run initialCache >>= fun trajectoryResult =>
          (simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run trajectoryResult.2) := by
      simp [map_eq_bind_pure_comp, bind_assoc]

noncomputable def Concrete.fixedSeedChainTrajectoriesFromCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    QueryCache HashSpec → List Epoch →
      ProbComp (List (Vector Digest (steps + 1)) × QueryCache HashSpec)
  | cache, [] => pure ([], cache)
  | cache, epoch :: epochs => do
      let first ← (simulateQ randomOracle
        (Concrete.chainTrajectory parameter epoch chain 0 steps
          (secret epoch chain))).run cache
      let rest ← Concrete.fixedSeedChainTrajectoriesFromCache
        parameter secret chain steps first.2 epochs
      return (first.1 :: rest.1, rest.2)

@[simp]
theorem Concrete.fixedSeedChainTrajectoriesFromCache_nil
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (cache : QueryCache HashSpec) :
    Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain steps
      cache [] = pure ([], cache) := rfl

theorem Concrete.fixedSeedChainTrajectoriesFromCache_cons
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (cache : QueryCache HashSpec)
    (epoch : Epoch) (epochs : List Epoch) :
    Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain steps
      cache (epoch :: epochs) = (do
        let first ← (simulateQ randomOracle
          (Concrete.chainTrajectory parameter epoch chain 0 steps
            (secret epoch chain))).run cache
        let rest ← Concrete.fixedSeedChainTrajectoriesFromCache
          parameter secret chain steps first.2 epochs
        return (first.1 :: rest.1, rest.2)) := rfl

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.fixedSeedChainTrajectoriesFromCache_support_info
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec)
      (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec),
      result ∈ support
        (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
          steps cache epochs) →
      cache ≤ result.2 ∧ result.1.length = epochs.length ∧
        List.Forall₂
          (fun epoch trajectory =>
            evalWithAnswerFn (Concrete.CacheReplay.answerFn result.2)
              (Concrete.chainTrajectory parameter epoch chain 0 steps
                (secret epoch chain)) = trajectory)
          epochs result.1 := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache result hresult
      simp only [Concrete.fixedSeedChainTrajectoriesFromCache_nil,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨le_rfl, rfl, List.Forall₂.nil⟩
  | cons epoch epochs ih =>
      intro cache result hresult
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      obtain ⟨hfirstCacheLe, hlength, hpairs⟩ :=
        ih first.2 rest hrest
      constructor
      · exact (Concrete.CacheReplay.randomOracle_cache_le
          (Concrete.chainTrajectory parameter epoch chain 0 steps
            (secret epoch chain)) cache first hfirst).trans hfirstCacheLe
      · constructor
        · simp [hlength]
        · apply List.Forall₂.cons
          · exact Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
              (Concrete.chainTrajectory parameter epoch chain 0 steps
                (secret epoch chain)) cache first.2 rest.2 first.1 hfirst
                hfirstCacheLe
          · exact hpairs

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.fixedSeedChainTrajectoriesFromCache_replay_in_largerCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    ∀ (epochs : List Epoch) (cache : QueryCache HashSpec)
      (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec)
      (largerCache : QueryCache HashSpec),
      result ∈ support
        (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
          steps cache epochs) →
      result.2 ≤ largerCache →
      List.Forall₂
        (fun epoch trajectory =>
          evalWithAnswerFn (Concrete.CacheReplay.answerFn largerCache)
            (Concrete.chainTrajectory parameter epoch chain 0 steps
              (secret epoch chain)) = trajectory)
        epochs result.1 := by
  intro epochs
  induction epochs with
  | nil =>
      intro cache result largerCache hresult _hle
      simp only [Concrete.fixedSeedChainTrajectoriesFromCache_nil,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact List.Forall₂.nil
  | cons epoch epochs ih =>
      intro cache result largerCache hresult hlarger
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      have hrestInfo :=
        Concrete.fixedSeedChainTrajectoriesFromCache_support_info parameter
          secret chain steps epochs first.2 rest hrest
      apply List.Forall₂.cons
      · exact Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
          (Concrete.chainTrajectory parameter epoch chain 0 steps
            (secret epoch chain)) cache first.2 largerCache first.1 hfirst
            (hrestInfo.1.trans hlarger)
      · exact ih first.2 rest largerCache hrest hlarger

theorem Concrete.fixedSeedChainTrajectoriesFromCache_table_eq_in_largerCache
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex)
    (result : List FullChainTrajectory × QueryCache HashSpec)
    (largerCache : QueryCache HashSpec)
    (hresult : result ∈ support
      (Concrete.fixedSeedChainTrajectoriesFromCache parameter secret chain
        (chainLength - 1) ∅ allEpochs))
    (hle : result.2 ≤ largerCache) :
    chainValueTableOfList result.1 =
      keygenChainValueTable largerCache (SecretKey.withoutPrecomputation parameter secret) chain := by
  have hinfo := Concrete.fixedSeedChainTrajectoriesFromCache_support_info
    parameter secret chain (chainLength - 1) allEpochs ∅ result hresult
  have hpairs :=
    Concrete.fixedSeedChainTrajectoriesFromCache_replay_in_largerCache
      parameter secret chain (chainLength - 1) allEpochs ∅ result largerCache
      hresult hle
  funext index
  unfold chainValueTableOfList
  split
  · rename_i htableLength
    let position := epochPosition index.1
    have hresultPosition : position.val < result.1.length := by
      rw [← htableLength]
      exact position.isLt
    have hpair := hpairs.get position.isLt hresultPosition
    have hepoch : allEpochs.get position = index.1 := by
      exact allEpochs_get_epochPosition index.1
    rw [hepoch] at hpair
    have hvalue := congrArg
      (fun trajectory : FullChainTrajectory =>
        trajectory[index.2.val]'(by
          have hdigit := index.2.isLt
          omega)) hpair
    rw [Concrete.chainTrajectory_getElem] at hvalue
    exact hvalue.symm
  · rename_i htableLength
    exact (htableLength hinfo.2.1.symm).elim

theorem evalDist_rootTree_run_eq_fixedSeedTrajectories_then_rootTree
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1)
    (epochs : List Epoch) (initialCache : QueryCache HashSpec) :
    evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run initialCache) =
      evalDist (Concrete.fixedSeedChainTrajectoriesFromCache
        parameter secret chain steps initialCache epochs >>= fun trajectoryResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run trajectoryResult.2) := by
  induction epochs generalizing initialCache with
  | nil =>
      simp
  | cons epoch epochs ih =>
      calc
        evalDist ((simulateQ randomOracle
            (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
              OracleComp HashSpec Digest)).run initialCache) =
            evalDist ((simulateQ randomOracle
              (Concrete.chainTrajectory parameter epoch chain 0 steps
                (secret epoch chain))).run initialCache >>= fun first =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run first.2) :=
          evalDist_rootTree_run_eq_chainTrajectory_then_rootTree
            parameter secret epoch chain steps hsteps initialCache
        _ = evalDist ((simulateQ randomOracle
              (Concrete.chainTrajectory parameter epoch chain 0 steps
                (secret epoch chain))).run initialCache >>= fun first =>
              Concrete.fixedSeedChainTrajectoriesFromCache
                parameter secret chain steps first.2 epochs >>= fun rest =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run rest.2) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          exact ih first.2
        _ = evalDist (Concrete.fixedSeedChainTrajectoriesFromCache parameter
              secret chain steps initialCache (epoch :: epochs) >>=
                fun trajectoryResult =>
              (simulateQ randomOracle
                (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                  OracleComp HashSpec Digest)).run trajectoryResult.2) := by
          rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons]
          simp only [bind_assoc, pure_bind]

noncomputable def chronologicallyWarmedExtractedFixedChainKeygen
    (chain : ChainIndex) : ProbComp ProgrammedFixedChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let secretView ← extractFixedChainSeeds chain allEpochs
  let secret := unflattenSecret secretView.2
  let rootResult ← (do
    let trajectoryResult ← Concrete.fixedSeedChainTrajectoriesFromCache
      parameter secret chain (chainLength - 1) ∅ allEpochs
    (simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run trajectoryResult.2)
  return {
    publicKey := ⟨rootResult.1, parameter⟩
    secretKey := (SecretKey.withoutPrecomputation parameter secret)
    cache := rootResult.2
    table := keygenChainValueTable rootResult.2 (SecretKey.withoutPrecomputation parameter secret) chain
  }

theorem evalDist_extractedFixedChainKeygen_eq_chronologicallyWarmed
    (chain : ChainIndex) :
    evalDist (extractedExplicitFixedChainKeygen chain) =
      evalDist (chronologicallyWarmedExtractedFixedChainKeygen chain) := by
  unfold extractedExplicitFixedChainKeygen
    chronologicallyWarmedExtractedFixedChainKeygen
    explicitFixedChainKeygenFromSecret
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro secretView
  let secret := unflattenSecret secretView.2
  let makeView : Digest × QueryCache HashSpec →
      ProbComp ProgrammedFixedChainKeygenView := fun rootResult =>
    pure ({
      publicKey := ⟨rootResult.1, parameter⟩
      secretKey := (SecretKey.withoutPrecomputation parameter secret)
      cache := rootResult.2
      table := keygenChainValueTable rootResult.2 (SecretKey.withoutPrecomputation parameter secret) chain
    } : ProgrammedFixedChainKeygenView)
  change evalDist ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run ∅ >>= makeView) =
    evalDist ((Concrete.fixedSeedChainTrajectoriesFromCache parameter secret
      chain (chainLength - 1) ∅ allEpochs >>= fun trajectoryResult =>
        (simulateQ randomOracle
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest)).run trajectoryResult.2) >>= makeView)
  conv_lhs => rw [evalDist_bind]
  conv_rhs => rw [evalDist_bind]
  rw [evalDist_rootTree_run_eq_fixedSeedTrajectories_then_rootTree
    parameter secret chain (chainLength - 1) le_rfl allEpochs ∅]

theorem evalDist_actualFixedChainKeygen_eq_chronologicallyWarmed
    (chain : ChainIndex) :
    evalDist (actualFixedChainKeygen chain) =
      evalDist (chronologicallyWarmedExtractedFixedChainKeygen chain) :=
  (evalDist_actualFixedChainKeygen_eq_extracted chain).trans
    (evalDist_extractedFixedChainKeygen_eq_chronologicallyWarmed chain)

end XmssSecurity
